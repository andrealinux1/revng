#
# This file is distributed under the MIT License. See LICENSE.md for details.
#

from collections import defaultdict
from graphlib import TopologicalSorter
from typing import Dict, List

from .definition import Definition
from .enum import EnumDefinition, EnumMember
from .struct import StructDefinition


class Schema:
    def __init__(self, raw_schema, base_namespace: str):
        self._raw_schema = raw_schema

        self.base_namespace = base_namespace
        self.generated_namespace = f"{base_namespace}::generated"

        # fully qualified name -> object
        self.definitions: Dict[str, Definition] = self._parse_definitions()
        self._generate_kinds()
        self._resolve_references()

    def get_definition_for(self, type_name):
        if self.definitions.get(type_name):
            return self.definitions.get(type_name)

        stripped_type_name = remove_prefix(type_name, f"{self.generated_namespace}::")
        stripped_type_name = remove_prefix(stripped_type_name, f"{self.base_namespace}::")

        if self.definitions.get(stripped_type_name):
            return self.definitions.get(stripped_type_name)

        if self.definitions.get(f"{self.base_namespace}::{stripped_type_name}"):
            return self.definitions.get(f"{self.base_namespace}::{stripped_type_name}")

        if self.definitions.get(f"{self.generated_namespace}::{stripped_type_name}"):
            return self.definitions.get(f"{self.generated_namespace}::{stripped_type_name}")

        return None

    def struct_definitions(self) -> List[StructDefinition]:
        toposorter: TopologicalSorter = TopologicalSorter()
        for struct in self.definitions.values():
            if not isinstance(struct, StructDefinition):
                continue

            toposorter.add(struct)

            for dependency in struct.dependencies:
                dep_type = self.get_definition_for(dependency)
                if isinstance(dep_type, StructDefinition):
                    toposorter.add(struct, dep_type)
                elif isinstance(dep_type, EnumDefinition) or dep_type is None:
                    pass
                else:
                    pass

        return list(toposorter.static_order())

    def enum_definitions(self) -> List[EnumDefinition]:
        return [enum for enum in self.definitions.values() if isinstance(enum, EnumDefinition)]

    def get_upcastable_types(self, base_type: StructDefinition):
        upcastable_types = set()
        for definition in self.struct_definitions():
            if definition.inherits is base_type:
                upcastable_types.add(definition)
        return upcastable_types

    def _parse_definitions(self):
        definitions = {}
        for type_schema in self._raw_schema:
            type_name = type_schema["type"]
            if type_name == "enum":
                cls = EnumDefinition
            elif type_name == "struct":
                cls = StructDefinition
            else:
                raise ValueError(f"Invalid type name: {type_name}")

            definition = cls.from_dict(type_schema, self.base_namespace)
            definitions[definition.fullname] = definition

        return definitions

    def _resolve_references(self):
        for t in self.definitions.values():
            t.resolve_references(self)

    def _generate_kinds(self):
        children = defaultdict(list)
        for _, value in self.definitions.items():
            if isinstance(value, StructDefinition) and value._inherits is not None:
                parent = self.get_definition_for(value._inherits)
                children[parent].append(value)

        for parent, child_list in children.items():
            kind_field = [f for f in parent.fields if f.name == "Kind"]
            if len(kind_field) == 0:
                raise ValueError("Kind field must be present in abstract classes")
            if kind_field[0].type != f"{parent.user_namespace}::{parent.name}Kind::Values":
                raise ValueError(
                    f"Kind field in {parent.name} must have the type "
                    + f"{parent.user_namespace}::{parent.name}Kind::Values'. "
                    + "This enum will be autogenerated with the child names "
                    + "of this class."
                )
            parent.children = child_list

            kind_enum_namespace = f"{parent.user_namespace}::{parent.name}Kind"
            kind_enum = EnumDefinition(
                namespace=kind_enum_namespace,
                user_namespace=kind_enum_namespace,
                name=f"{parent.name}Kind",
                members=[EnumMember(name=c.name) for c in child_list],
            )
            kind_enum.autogenerated = True
            self.definitions[f"{kind_enum_namespace}::Values"] = kind_enum


def remove_prefix(s: str, prefix: str):
    if s.startswith(prefix):
        return s[len(prefix) :]
    return s
