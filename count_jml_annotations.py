#!/usr/bin/env python3

import os
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import TypedDict


class JMLStats(TypedDict):
    classes_with_jml: set[str]
    methods_with_jml: int
    subclasses_with_jml: set[str]
    interfaces_abstract_with_jml: set[str]
    classes_implementing_interfaces_with_jml: set[str]
    invariant: int
    initially: int
    constraint: int
    requires: int
    ensures: int
    assignable_assigns: int
    pure: int
    helper: int
    normal_behavior: int
    exceptional_behavior: int
    signals_only: int
    also: int
    forall: int
    exists: int
    assert_: int
    loops_specified: int
    models_represents: int


@dataclass(frozen=True)
class Patterns:
    jml: re.Pattern = re.compile(r'^\s*//\s*@|^\s*/\*\s*@')
    method: re.Pattern = re.compile(
        r'^\s*(public|private|protected|)\s*(static\s+)?(abstract\s+)?'
        r'([a-zA-Z<>\[\]_,\s]+\s+)?([a-zA-Z_][a-zA-Z0-9_]*)\s*\('
    )
    class_: re.Pattern = re.compile(
        r'^\s*(public|private|protected)?\s*(abstract|final)?\s*'
        r'(class|interface|enum)\s+([a-zA-Z_][a-zA-Z0-9_]*)'
    )
    extends: re.Pattern = re.compile(r'\s+extends\s+([a-zA-Z_][a-zA-Z0-9_]*)')
    implements: re.Pattern = re.compile(r'\s+implements\s+([a-zA-Z_][a-zA-Z0-9_,\s]*)')
    loop_annotation: re.Pattern = re.compile(
        r'//\s*@\s*(loop_invariant|maintaining|decreases|decreasing)'
    )


def _count_annotation(line: str, pattern: str, stats: JMLStats, key: str) -> None:
    if re.search(pattern, line):
        stats[key] += 1


def _process_jml_line(line: str, stats: JMLStats, patterns: Patterns) -> None:
    annotation_map = {
        r'//\s*@.*\binvariant\b': 'invariant',
        r'//\s*@.*\binitially\b': 'initially',
        r'//\s*@.*\bconstraint\b': 'constraint',
        r'//\s*@.*\brequires\b': 'requires',
        r'//\s*@.*\bensures\b': 'ensures',
        r'//\s*@.*\b(assignable|assigns)\b': 'assignable_assigns',
        r'//\s*@.*\bpure\b': 'pure',
        r'//\s*@.*\bhelper\b': 'helper',
        r'//\s*@.*\b(normal_behavior|normal_behaviour)\b': 'normal_behavior',
        r'//\s*@.*\b(exceptional_behavior|exceptional_behaviour)\b': 'exceptional_behavior',
        r'//\s*@.*\bsignals_only\b': 'signals_only',
        r'//\s*@.*\balso\b': 'also',
        r'\\forall\b': 'forall',
        r'\\exists\b': 'exists',
        r'//\s*@.*\bassert\b': 'assert_',
        r'//\s*@.*\brepresents\b': 'models_represents',
    }
    
    for pattern, key in annotation_map.items():
        _count_annotation(line, pattern, stats, key)
    
    if patterns.loop_annotation.search(line):
        stats['loops_specified'] += 1


def count_jml_annotations(src_dir: Path) -> JMLStats:
    stats: JMLStats = {
        'classes_with_jml': set(),
        'methods_with_jml': 0,
        'subclasses_with_jml': set(),
        'interfaces_abstract_with_jml': set(),
        'classes_implementing_interfaces_with_jml': set(),
        'invariant': 0,
        'initially': 0,
        'constraint': 0,
        'requires': 0,
        'ensures': 0,
        'assignable_assigns': 0,
        'pure': 0,
        'helper': 0,
        'normal_behavior': 0,
        'exceptional_behavior': 0,
        'signals_only': 0,
        'also': 0,
        'forall': 0,
        'exists': 0,
        'assert_': 0,
        'loops_specified': 0,
        'models_represents': 0,
    }
    
    patterns = Patterns()
    
    for java_file in src_dir.rglob('*.java'):
        try:
            content = java_file.read_text(encoding='utf-8')
        except UnicodeDecodeError:
            content = java_file.read_text(encoding='utf-8', errors='ignore')
        
        lines = content.splitlines()
        has_jml_before_method = False
        has_jml_in_class = False
        current_class = None
        is_abstract_or_interface = False
        extends_class = False
        implements_interface = False
        
        for line in lines:
            if patterns.jml.match(line):
                has_jml_in_class = True
                has_jml_before_method = True
                _process_jml_line(line, stats, patterns)
            
            elif class_match := patterns.class_.match(line):
                current_class = class_match.group(4)
                class_type = class_match.group(3)
                is_abstract_or_interface = (
                    class_match.group(2) == 'abstract' or class_type == 'interface'
                )
                extends_class = bool(patterns.extends.search(line))
                implements_interface = bool(patterns.implements.search(line))
            
            elif patterns.method.match(line):
                if has_jml_before_method:
                    stats['methods_with_jml'] += 1
                    has_jml_before_method = False
            
            elif line.strip() and not line.strip().startswith('//'):
                if not patterns.jml.match(line):
                    has_jml_before_method = False
        
        if has_jml_in_class and current_class:
            stats['classes_with_jml'].add(current_class)
            
            if extends_class:
                stats['subclasses_with_jml'].add(current_class)
            
            if is_abstract_or_interface:
                stats['interfaces_abstract_with_jml'].add(current_class)
            
            if implements_interface:
                stats['classes_implementing_interfaces_with_jml'].add(current_class)
    
    return stats



def print_report(stats: JMLStats) -> None:
    separator = "=" * 80
    print(separator)
    print("RELATÓRIO DE ANOTAÇÕES JML - PROJETO CHESS-OPENJML")
    print(separator)
    print()
    
    print("MÉTRICAS DE ESTRUTURA:")
    print(f"  Número de Classes com Anotações JML: {len(stats['classes_with_jml'])}")
    print(f"  Quantidade de Métodos com Anotações JML: {stats['methods_with_jml']}")
    print(f"  Quantidade de Subclasses com Anotações JML (Especificação de Herança): "
          f"{len(stats['subclasses_with_jml'])}")
    print(f"  Quantidade de Interfaces/Classes Abstratas com Anotações JML: "
          f"{len(stats['interfaces_abstract_with_jml'])}")
    print(f"  Quantidade de Classes que Implementam Interfaces com Anotações JML: "
          f"{len(stats['classes_implementing_interfaces_with_jml'])}")
    print()
    
    print("ANOTAÇÕES JML:")
    print(f"  invariant: {stats['invariant']}")
    print(f"  initially: {stats['initially']}")
    print(f"  constraint: {stats['constraint']}")
    print(f"  requires: {stats['requires']}")
    print(f"  ensures: {stats['ensures']}")
    print(f"  assignable/assigns: {stats['assignable_assigns']}")
    print(f"  pure: {stats['pure']}")
    print(f"  helper: {stats['helper']}")
    print(f"  normal_behavior: {stats['normal_behavior']}")
    print(f"  exceptional_behavior: {stats['exceptional_behavior']}")
    print(f"  signals_only: {stats['signals_only']}")
    print(f"  also: {stats['also']}")
    print()
    
    print("QUANTIFICADORES E EXPRESSÕES:")
    print(f"  \\forall: {stats['forall']}")
    print(f"  \\exists: {stats['exists']}")
    print(f"  assert: {stats['assert_']}")
    print()
    
    print("ESPECIFICAÇÕES AVANÇADAS:")
    print(f"  Loops especificados: {stats['loops_specified']}")
    print(f"  Modelos (represents): {stats['models_represents']}")
    print()
    print(separator)


def main() -> None:
    src_dir = Path(sys.argv[1]) if len(sys.argv) > 1 else Path('src/main')
    
    if not src_dir.exists():
        print(f"Erro: Diretório '{src_dir}' não encontrado!")
        sys.exit(1)
    
    print(f"Analisando código em: {src_dir}")
    print()
    
    stats = count_jml_annotations(src_dir)
    print_report(stats)


if __name__ == '__main__':
    main()

