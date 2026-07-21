#!/usr/bin/env python3
"""Generate the finite second-stage Parts gadget and its coloring trees.

The 73 vertices are two radius-three triangular-lattice patches with a common
origin.  The second patch is rotated through arccos(7/8); combinatorially, the
patches have six additional unit edges joining corresponding radius-two
vertices.  The certificate trees prove that the opposite radius-two vertices
(-2, 0) and (2, 0) receive the same color whenever unit edges are proper and
every sqrt-three equilateral triple is non-monochromatic.

This script is deterministic.  It uses only integer axial-lattice arithmetic;
the Euclidean realization and all certificate soundness claims are proved in
Lean.
"""

from __future__ import annotations

from pathlib import Path
from typing import Iterable, List, Optional, Sequence, Tuple

from parts_gadget_model import (
    EDGES,
    INDEX,
    LABELS,
    NEGATION,
    NEIGHBORS,
    N,
    TRIPLES,
    TRIPLE_PAIRS,
    TRIPLE_WITNESSES,
    Assignment,
    CaseBranch,
    CaseLeaf,
    TreeNode,
    blocked,
    build_tree,
)


ROOT = Path(__file__).resolve().parents[1]
LEAN_DIR = ROOT / "HadwigerNelsonBounds"
COPYRIGHT = """/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
"""

def lean_list(values: Iterable[str]) -> str:
    return "[" + ", ".join(values) + "]"


def write_data() -> None:
    lines = [
        COPYRIGHT.rstrip(),
        "",
        "import HadwigerNelsonBounds.PartsCanonicalTriangle",
        "",
        "/-! Generated exact combinatorics for the finite second-stage Parts gadget. -/",
        "",
        "namespace HadwigerNelsonBounds",
        "",
        "/-- Axial coordinates in one of the two triangular-lattice patches. -/",
        "structure PartsGadgetVertex where",
        "  /-- Whether the point lies in the rotated patch. -/ rotated : Bool",
        "  /-- First axial coordinate. -/ q : Int",
        "  /-- Second axial coordinate. -/ r : Int",
        "deriving DecidableEq",
        "",
        "/-- Exact descriptor of one of the 73 gadget vertices. -/",
        "def partsGadgetVertex (vertex : Fin 73) : PartsGadgetVertex :=",
        "  match vertex.val with",
    ]
    for index, (patch, q, r) in enumerate(LABELS):
        lines.append(f"  | {index} => ⟨{str(bool(patch)).lower()}, {q}, {r}⟩")
    lines.append("  | _ => ⟨false, 0, 0⟩")
    lines += [
        "",
        "/-- Raw geometric witness for one listed sqrt-three triple. -/",
        "structure PartsGadgetTriangleWitnessData where",
        "  /-- First partner of the rooted triple. -/ left : Fin 73",
        "  /-- Second partner of the rooted triple. -/ right : Fin 73",
        "  /-- Vertex in the canonical A role. -/ a : Fin 73",
        "  /-- Vertex in the canonical B role. -/ b : Fin 73",
        "  /-- Vertex in the canonical C role. -/ c : Fin 73",
        "  /-- Patch containing the triple. -/ rotated : Bool",
        "  /-- First axial coordinate of its center. -/ centerQ : Int",
        "  /-- Second axial coordinate of its center. -/ centerR : Int",
        "  /-- Whether the canonical triangle is inverted. -/ negated : Bool",
        "deriving DecidableEq",
        "",
        "/-- A vertex has the requested axial coordinates in the requested patch.",
        "The common origin belongs to both patches. -/",
        "def partsGadgetAxialAt (rotated : Bool) (q r : Int)",
        "    (vertex : Fin 73) : Prop :=",
        "  let descriptor := partsGadgetVertex vertex",
        "  descriptor.q = q ∧ descriptor.r = r ∧",
        "    (descriptor.rotated = rotated ∨ (q = 0 ∧ r = 0))",
        "",
        "instance (rotated : Bool) (q r : Int) (vertex : Fin 73) :",
        "    Decidable (partsGadgetAxialAt rotated q r vertex) := by",
        "  unfold partsGadgetAxialAt",
        "  infer_instance",
        "",
        "/-- Decidable equality-up-to-permutation for three named vertices. -/",
        "def partsGadgetSameTriple (a b c x y z : Fin 73) : Prop :=",
        "  (a = x ∧ b = y ∧ c = z) ∨ (a = x ∧ b = z ∧ c = y) ∨",
        "    (a = y ∧ b = x ∧ c = z) ∨ (a = y ∧ b = z ∧ c = x) ∨",
        "    (a = z ∧ b = x ∧ c = y) ∨ (a = z ∧ b = y ∧ c = x)",
        "",
        "instance (a b c x y z : Fin 73) :",
        "    Decidable (partsGadgetSameTriple a b c x y z) := by",
        "  unfold partsGadgetSameTriple",
        "  infer_instance",
        "",
        "/-- Exact validity conditions for a triangle witness. -/",
        "def PartsGadgetTriangleWitnessData.Valid",
        "    (witness : PartsGadgetTriangleWitnessData) (root : Fin 73) : Prop :=",
        "  partsGadgetSameTriple witness.a witness.b witness.c",
        "      root witness.left witness.right ∧",
        "    partsGadgetAxialAt witness.rotated",
        "      (witness.centerQ + if witness.negated then -1 else 1)",
        "      witness.centerR witness.a ∧",
        "    partsGadgetAxialAt witness.rotated witness.centerQ",
        "      (witness.centerR + if witness.negated then 1 else -1)",
        "      witness.b ∧",
        "    partsGadgetAxialAt witness.rotated",
        "      (witness.centerQ + if witness.negated then 1 else -1)",
        "      (witness.centerR + if witness.negated then -1 else 1)",
        "      witness.c",
        "",
        "instance (witness : PartsGadgetTriangleWitnessData) (root : Fin 73) :",
        "    Decidable (witness.Valid root) := by",
        "  unfold PartsGadgetTriangleWitnessData.Valid",
        "  infer_instance",
        "",
        "/-- Geometric witnesses for every listed sqrt-three triple. -/",
        "def partsGadgetTriangleWitnesses (vertex : Fin 73) :",
        "    List PartsGadgetTriangleWitnessData :=",
        "  match vertex.val with",
    ]
    for index, witnesses in enumerate(TRIPLE_WITNESSES):
        lines.append(f"  | {index} => [")
        for witness in witnesses:
            left, right, a, b, c, rotated, cq, cr, negated = witness
            lines.append(
                "    ⟨"
                f"{left}, {right}, {a}, {b}, {c}, "
                f"{str(rotated).lower()}, {cq}, {cr}, {str(negated).lower()}"
                "⟩,"
            )
        lines.append("  ]")
    lines.append("  | _ => []")
    lines += [
        "",
        "/-- Unit-edge neighbors used by the executable certificate checker. -/",
        "def partsGadgetNeighbors (vertex : Fin 73) : List (Fin 73) :=",
        "  match vertex.val with",
    ]
    for index, neighbors in enumerate(NEIGHBORS):
        lines.append(f"  | {index} => {lean_list(map(str, neighbors))}")
    lines.append("  | _ => []")
    lines += [
        "",
        "/-- Opposite pairs completing sqrt-three triples at a vertex. -/",
        "def partsGadgetTriplePairs (vertex : Fin 73) : List (Fin 73 × Fin 73) :=",
        "  (partsGadgetTriangleWitnesses vertex).map fun witness =>",
        "    (witness.left, witness.right)",
    ]
    lines += [
        "",
        "/-- Central inversion of both lattice patches. -/",
        "def partsGadgetNegation (vertex : Fin 73) : Fin 73 :=",
        "  match vertex.val with",
    ]
    for index, image in enumerate(NEGATION):
        lines.append(f"  | {index} => {image}")
    lines.append("  | _ => 18")
    lines += ["", "end HadwigerNelsonBounds", ""]
    (LEAN_DIR / "PartsGadgetData.lean").write_text("\n".join(lines))


def write_symmetry_files() -> int:
    groups = [list(range(start, min(start + 19, N))) for start in range(0, N, 19)]
    for file_index, indices in enumerate(groups):
        lines = [
            COPYRIGHT.rstrip(),
            "",
            "import HadwigerNelsonBounds.PartsGadgetData",
            "",
            f"/-! Generated central-inversion checks, group {file_index}. -/",
            "",
            "namespace HadwigerNelsonBounds",
            "",
        ]
        for index in indices:
            neighbor_cases = " | ".join("rfl" for _ in NEIGHBORS[index])
            triple_cases = " | ".join("rfl" for _ in TRIPLE_PAIRS[index])
            neighbor_list = lean_list(map(str, NEIGHBORS[index]))
            triple_list = lean_list(
                f"({left}, {right})" for left, right in TRIPLE_PAIRS[index]
            )
            triple_change = f"  change pair ∈ {triple_list} at hpair"
            if len(triple_change) > 100:
                entries = "\n".join(
                    f"    ({left}, {right}),"
                    for left, right in TRIPLE_PAIRS[index]
                )
                triple_change = f"  change pair ∈ [\n{entries}\n  ] at hpair"
            lines += [
                f"lemma partsGadgetNegationNeighbor{index} {{neighbor : Fin 73}}",
                f"    (hadj : neighbor ∈ partsGadgetNeighbors {index}) :",
                "    partsGadgetNegation neighbor ∈",
                f"      partsGadgetNeighbors (partsGadgetNegation {index}) := by",
                f"  change neighbor ∈ {neighbor_list} at hadj",
                "  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj",
                f"  rcases hadj with {neighbor_cases}",
                "  all_goals decide",
                "",
                f"lemma partsGadgetNegationTriple{index} {{pair : Fin 73 × Fin 73}}",
                f"    (hpair : pair ∈ partsGadgetTriplePairs {index}) :",
                "    (partsGadgetNegation pair.1, partsGadgetNegation pair.2) ∈",
                f"        partsGadgetTriplePairs (partsGadgetNegation {index}) ∨",
                "      (partsGadgetNegation pair.2, partsGadgetNegation pair.1) ∈",
                f"        partsGadgetTriplePairs (partsGadgetNegation {index}) := by",
                triple_change,
                "  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair",
                f"  rcases hpair with {triple_cases}",
                "  all_goals decide",
                "",
                f"lemma partsGadgetTriangleWitnessValid{index}",
                "    {witness : PartsGadgetTriangleWitnessData}",
                "    (hwitness : witness ∈ partsGadgetTriangleWitnesses "
                f"{index}) : witness.Valid {index} := by",
                "  change witness ∈ [",
            ]
            for witness in TRIPLE_WITNESSES[index]:
                left, right, a, b, c, rotated, cq, cr, negated = witness
                lines.append(
                    "    ⟨"
                    f"{left}, {right}, {a}, {b}, {c}, "
                    f"{str(rotated).lower()}, {cq}, {cr}, {str(negated).lower()}"
                    "⟩,"
                )
            lines += [
                "  ] at hwitness",
                "  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwitness",
                f"  rcases hwitness with {triple_cases}",
                "  all_goals decide",
                "",
            ]
        lines += ["end HadwigerNelsonBounds", ""]
        path = LEAN_DIR / f"PartsGadgetSymmetry{file_index}.lean"
        path.write_text("\n".join(lines))

    lines = [
        COPYRIGHT.rstrip(),
        "",
        *(
            f"import HadwigerNelsonBounds.PartsGadgetSymmetry{index}"
            for index in range(len(groups))
        ),
        "",
        "/-! Aggregated central-inversion facts for the finite gadget. -/",
        "",
        "namespace HadwigerNelsonBounds",
        "",
        "lemma partsGadgetNegation_neighbor {vertex neighbor : Fin 73}",
        "    (hadj : neighbor ∈ partsGadgetNeighbors vertex) :",
        "    partsGadgetNegation neighbor ∈",
        "      partsGadgetNeighbors (partsGadgetNegation vertex) := by",
        "  fin_cases vertex",
    ]
    for index in range(N):
        lines.append(f"  · exact partsGadgetNegationNeighbor{index} hadj")
    lines += [
        "",
        "lemma partsGadgetNegation_triple {vertex : Fin 73}",
        "    {pair : Fin 73 × Fin 73}",
        "    (hpair : pair ∈ partsGadgetTriplePairs vertex) :",
        "    (partsGadgetNegation pair.1, partsGadgetNegation pair.2) ∈",
        "        partsGadgetTriplePairs (partsGadgetNegation vertex) ∨",
        "      (partsGadgetNegation pair.2, partsGadgetNegation pair.1) ∈",
        "        partsGadgetTriplePairs (partsGadgetNegation vertex) := by",
        "  fin_cases vertex",
    ]
    for index in range(N):
        lines.append(f"  · exact partsGadgetNegationTriple{index} hpair")
    lines += [
        "",
        "lemma partsGadgetTriangleWitness_valid {vertex : Fin 73}",
        "    {witness : PartsGadgetTriangleWitnessData}",
        "    (hwitness : witness ∈ partsGadgetTriangleWitnesses vertex) :",
        "    witness.Valid vertex := by",
        "  fin_cases vertex",
    ]
    for index in range(N):
        lines.append(f"  · exact partsGadgetTriangleWitnessValid{index} hwitness")
    lines += ["", "end HadwigerNelsonBounds", ""]
    (LEAN_DIR / "PartsGadgetSymmetry.lean").write_text("\n".join(lines))
    return len(groups) + 1


def write_edge_verification_files() -> int:
    groups = [list(range(start, min(start + 19, N))) for start in range(0, N, 19)]
    for file_index, indices in enumerate(groups):
        lines = [
            COPYRIGHT.rstrip(),
            "",
            "import HadwigerNelsonBounds.PartsGadgetEmbeddingCore",
            "",
            f"/-! Generated edge-geometry checks, group {file_index}. -/",
            "",
            "namespace HadwigerNelsonBounds",
            "",
        ]
        for index in indices:
            neighbor_cases = " | ".join("rfl" for _ in NEIGHBORS[index])
            neighbor_list = lean_list(map(str, NEIGHBORS[index]))
            lines += [
                f"lemma partsGadgetEdgeCase{index} {{neighbor : Fin 73}}",
                f"    (hadj : neighbor ∈ partsGadgetNeighbors {index}) :",
                f"    PartsGadgetEdgeCase {index} neighbor := by",
                f"  change neighbor ∈ {neighbor_list} at hadj",
                "  simp only [List.mem_cons, List.not_mem_nil, or_false] at hadj",
                f"  rcases hadj with {neighbor_cases}",
                "  all_goals decide",
                "",
            ]
        lines += ["end HadwigerNelsonBounds", ""]
        path = LEAN_DIR / f"PartsGadgetEdgeVerification{file_index}.lean"
        path.write_text("\n".join(lines))

    lines = [
        COPYRIGHT.rstrip(),
        "",
        *(
            f"import HadwigerNelsonBounds.PartsGadgetEdgeVerification{index}"
            for index in range(len(groups))
        ),
        "",
        "/-! Aggregated edge-geometry checks for the finite gadget. -/",
        "",
        "namespace HadwigerNelsonBounds",
        "",
        "lemma partsGadget_edgeCase {vertex neighbor : Fin 73}",
        "    (hadj : neighbor ∈ partsGadgetNeighbors vertex) :",
        "    PartsGadgetEdgeCase vertex neighbor := by",
        "  fin_cases vertex",
    ]
    for index in range(N):
        lines.append(f"  · exact partsGadgetEdgeCase{index} hadj")
    lines += ["", "end HadwigerNelsonBounds", ""]
    (LEAN_DIR / "PartsGadgetEdgeVerification.lean").write_text("\n".join(lines))
    return len(groups) + 1


def format_assignment(assignment: Assignment) -> str:
    return f"⟨{assignment[0]}, {assignment[1]}⟩"


def format_node(node: TreeNode) -> List[str]:
    children = [0 if child is None else child + 1 for child in node.children]
    if len(node.stem) <= 4:
        stem = lean_list(format_assignment(item) for item in node.stem)
        return [
            f"  ⟨{stem}, {node.vertex}, ![{', '.join(map(str, children))}]⟩,"
        ]
    result = ["  ⟨["]
    for start in range(0, len(node.stem), 5):
        group = ", ".join(
            format_assignment(item) for item in node.stem[start : start + 5]
        )
        suffix = "," if start + 5 < len(node.stem) else ""
        result.append(f"    {group}{suffix}")
    result.append(
        f"  ], {node.vertex}, ![{', '.join(map(str, children))}]⟩,"
    )
    return result


def write_tree_files(name: str, roots: Sequence[Assignment], nodes: List[TreeNode]) -> int:
    chunks = [nodes[start : start + 64] for start in range(0, len(nodes), 64)]
    chunks_per_file = 2
    file_count = (len(chunks) + chunks_per_file - 1) // chunks_per_file
    for file_index in range(file_count):
        first = file_index * chunks_per_file
        selected = chunks[first : first + chunks_per_file]
        lines = [
            COPYRIGHT.rstrip(),
            "",
            "import HadwigerNelsonBounds.PartsGadgetCertificate",
            "",
            f"/-! Generated `{name}` certificate chunks {first} through {first + len(selected) - 1}. -/",
            "",
            "namespace HadwigerNelsonBounds",
            "",
        ]
        for offset, chunk in enumerate(selected):
            chunk_index = first + offset
            lines += [
                f"/-- `{name}` certificate chunk {chunk_index}. -/",
                f"def partsGadget{name}Chunk{chunk_index} : Array PartsGadgetTreeNode := #[",
            ]
            for node in chunk:
                lines.extend(format_node(node))
            lines += ["]", ""]
        lines += ["end HadwigerNelsonBounds", ""]
        path = LEAN_DIR / f"PartsGadget{name}Data{file_index}.lean"
        path.write_text("\n".join(lines))

    imports = [
        f"import HadwigerNelsonBounds.PartsGadget{name}Data{index}"
        for index in range(file_count)
    ]
    chunk_names = [f"partsGadget{name}Chunk{index}" for index in range(len(chunks))]
    lines = [
        COPYRIGHT.rstrip(),
        "",
        *imports,
        "",
        f"/-! Aggregation of the generated `{name}` certificate. -/",
        "",
        "namespace HadwigerNelsonBounds",
        "",
        f"/-- The checked `{name}` contradiction tree. -/",
        f"def partsGadget{name}Certificate : PartsGadgetCertificate := {{",
        "  roots := " + lean_list(format_assignment(item) for item in roots),
        f"  nodeCount := {len(nodes)}",
        "  nodes := #[",
    ]
    lines += [f"    {chunk}," for chunk in chunk_names]
    lines += ["  ]", "}", "", "end HadwigerNelsonBounds", ""]
    (LEAN_DIR / f"PartsGadget{name}Data.lean").write_text("\n".join(lines))
    return file_count


def partition_tree(
    roots: Sequence[Assignment], threshold: int
) -> Tuple[object, List[Tuple[List[Assignment], List[TreeNode]]]]:
    leaves: List[Tuple[List[Assignment], List[TreeNode]]] = []

    def visit(path: List[Assignment]) -> object:
        tree = build_tree(path)
        if len(tree) <= threshold:
            index = len(leaves)
            leaves.append((path, tree))
            return CaseLeaf(index)

        vertex = tree[0].vertex
        assigned = dict(path)
        children: List[Optional[object]] = []
        for color in range(4):
            if blocked(assigned, vertex, color):
                children.append(None)
            else:
                children.append(visit(path + [(vertex, color)]))
        return CaseBranch(vertex, children)

    return visit(list(roots)), leaves


def format_certificate_definition(
    name: str, roots: Sequence[Assignment], nodes: List[TreeNode]
) -> List[str]:
    chunks = [nodes[start : start + 64] for start in range(0, len(nodes), 64)]
    lines = [
        f"/-- Independently checked hard-case certificate `{name}`. -/",
        f"def {name} : PartsGadgetCertificate := {{",
        "  roots := [",
    ]
    for start in range(0, len(roots), 6):
        group = ", ".join(
            format_assignment(item) for item in roots[start : start + 6]
        )
        suffix = "," if start + 6 < len(roots) else ""
        lines.append(f"    {group}{suffix}")
    lines += [
        "  ]",
        f"  nodeCount := {len(nodes)}",
        "  nodes := #[",
    ]
    for chunk in chunks:
        lines.append("    #[")
        lines.extend("    " + line for node in chunk for line in format_node(node))
        lines.append("    ],")
    lines += ["  ]", "}", ""]
    return lines


def flatten_cases(root: object) -> List[Tuple[str, int, List[int]]]:
    result: List[Optional[Tuple[str, int, List[int]]]] = []

    def visit(node: object) -> int:
        index = len(result)
        result.append(None)
        if isinstance(node, CaseLeaf):
            result[index] = ("leaf", node.certificate, [])
        elif isinstance(node, CaseBranch):
            children = [0 if child is None else visit(child) + 1 for child in node.children]
            result[index] = ("branch", node.vertex, children)
        else:
            raise TypeError(node)
        return index

    if visit(root) != 0 or any(node is None for node in result):
        raise RuntimeError("malformed case tree")
    return [node for node in result if node is not None]


def write_hard_cases(roots: Sequence[Assignment]) -> Tuple[int, int]:
    root, leaves = partition_tree(roots, threshold=150)
    groups: List[List[str]] = []
    current: List[str] = []
    for index, (leaf_roots, nodes) in enumerate(leaves):
        definition = format_certificate_definition(
            f"partsGadgetHardCertificate{index}", leaf_roots, nodes
        )
        if current and len(current) + len(definition) > 560:
            groups.append(current)
            current = []
        current.extend(definition)
    if current:
        groups.append(current)

    for file_index, definitions in enumerate(groups):
        lines = [
            COPYRIGHT.rstrip(),
            "",
            "import HadwigerNelsonBounds.PartsGadgetCases",
            "",
            f"/-! Generated hard-case certificates, data group {file_index}. -/",
            "",
            "namespace HadwigerNelsonBounds",
            "",
            *definitions,
            "end HadwigerNelsonBounds",
            "",
        ]
        (LEAN_DIR / f"PartsGadgetHardCasesData{file_index}.lean").write_text(
            "\n".join(lines)
        )

    imports = [
        f"import HadwigerNelsonBounds.PartsGadgetHardCasesData{index}"
        for index in range(len(groups))
    ]
    case_nodes = flatten_cases(root)
    count = len(leaves)
    lines = [
        COPYRIGHT.rstrip(),
        "",
        *imports,
        "",
        "/-! Generated aggregation and routing for the hard normalized cases. -/",
        "",
        "namespace HadwigerNelsonBounds",
        "",
        "/-- All independently checked hard-case certificates. -/",
        f"def partsGadgetHardCertificates (index : Fin {count}) : PartsGadgetCertificate :=",
        "  match index.val with",
    ]
    for index in range(count):
        lines.append(f"  | {index} => partsGadgetHardCertificate{index}")
    lines.append("  | _ => partsGadgetHardCertificate0")
    lines += [
        "",
        "/-- Routing nodes covering every unblocked hard normalized coloring. -/",
        f"def partsGadgetHardCaseNodes : Array (PartsGadgetCaseNode {count}) := #[",
    ]
    for kind, value, children in case_nodes:
        if kind == "leaf":
            lines.append(f"  PartsGadgetCaseNode.leaf {value},")
        else:
            lines.append(
                f"  PartsGadgetCaseNode.branch {value} "
                f"![{', '.join(map(str, children))}],"
            )
    lines += [
        "]",
        "",
        "/-- The complete hard-case routing tree. -/",
        f"def partsGadgetHardCaseTree : PartsGadgetCaseTree {count} := {{",
        "  roots := " + lean_list(format_assignment(item) for item in roots),
        f"  nodeCount := {len(case_nodes)}",
        "  nodes := partsGadgetHardCaseNodes",
        "}",
        "",
        "end HadwigerNelsonBounds",
        "",
    ]
    (LEAN_DIR / "PartsGadgetHardCasesData.lean").write_text("\n".join(lines))

    verification_groups = [
        list(range(start, min(start + 4, count)))
        for start in range(0, count, 4)
    ]
    for file_index, indices in enumerate(verification_groups):
        lines = [
            COPYRIGHT.rstrip(),
            "",
            "import HadwigerNelsonBounds.PartsGadgetHardCasesData",
            "",
            f"/-! Kernel checks for hard-case certificate group {file_index}. -/",
            "",
            "namespace HadwigerNelsonBounds",
            "",
        ]
        for index in indices:
            lines += [
                f"theorem partsGadgetHardCertificate{index}_verifies :",
                f"    partsGadgetHardCertificate{index}.Verifies := by",
                "  decide",
                "",
            ]
        lines += ["end HadwigerNelsonBounds", ""]
        path = LEAN_DIR / f"PartsGadgetHardVerification{file_index}.lean"
        path.write_text("\n".join(lines))

    lines = [
        COPYRIGHT.rstrip(),
        "",
        *(
            f"import HadwigerNelsonBounds.PartsGadgetHardVerification{index}"
            for index in range(len(verification_groups))
        ),
        "",
        "/-! Aggregated kernel and routing checks for the hard normalized cases. -/",
        "",
        "namespace HadwigerNelsonBounds",
        "",
        "/-- Every hard-case leaf certificate has been kernel checked. -/",
        f"theorem partsGadgetHardCertificates_verify (index : Fin {count}) :",
        "    (partsGadgetHardCertificates index).Verifies := by",
        "  fin_cases index",
    ]
    for index in range(count):
        lines.append(f"  · exact partsGadgetHardCertificate{index}_verifies")
    lines += [
        "",
        "/-- The case router covers every unblocked normalized color. -/",
        "theorem partsGadgetHardCaseTree_verifiesRouting :",
        "    partsGadgetHardCaseTree.VerifiesRouting partsGadgetHardCertificates := by",
        "  decide",
        "",
        "end HadwigerNelsonBounds",
        "",
    ]
    (LEAN_DIR / "PartsGadgetHardVerification.lean").write_text("\n".join(lines))
    return len(groups), count


def main() -> None:
    if N != 73 or len(EDGES) != 186 or len(TRIPLES) != 76:
        raise RuntimeError((N, len(EDGES), len(TRIPLES)))
    endpoint_a = INDEX[(0, -2, 0)]
    endpoint_b = INDEX[(0, 2, 0)]
    center = INDEX[(0, 0, 0)]
    anchor = INDEX[(0, 1, 0)]
    if (endpoint_a, endpoint_b, center, anchor) != (5, 31, 18, 25):
        raise RuntimeError((endpoint_a, endpoint_b, center, anchor))

    write_data()
    symmetry_files = write_symmetry_files()
    edge_files = write_edge_verification_files()
    hard_roots = [(endpoint_a, 0), (endpoint_b, 3), (center, 0), (anchor, 1)]
    middle_roots = [(endpoint_a, 0), (endpoint_b, 3), (center, 1)]
    middle = build_tree(middle_roots)
    hard_files, hard_count = write_hard_cases(hard_roots)
    middle_files = write_tree_files("Middle", middle_roots, middle)
    print(
        "generated",
        f"vertices={N}",
        f"edges={len(EDGES)}",
        f"triples={len(TRIPLES)}",
        f"hard_certificates={hard_count}",
        f"middle_nodes={len(middle)}",
        f"data_files={hard_files + middle_files + symmetry_files + edge_files + 4}",
    )


if __name__ == "__main__":
    main()
