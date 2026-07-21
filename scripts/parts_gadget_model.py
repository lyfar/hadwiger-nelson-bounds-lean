"""Integer model and deterministic coloring search for the Parts gadget."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Dict, List, Optional, Sequence, Tuple


Coord = Tuple[int, int]
Label = Tuple[int, int, int]
Assignment = Tuple[int, int]


def axial_norm_sq(a: Coord, b: Coord = (0, 0)) -> int:
    q = a[0] - b[0]
    r = a[1] - b[1]
    return q * q + q * r + r * r


AXIAL_POINTS: List[Coord] = sorted(
    (q, r)
    for q in range(-3, 4)
    for r in range(-3, 4)
    if max(abs(q), abs(r), abs(q + r)) <= 3
)

# The common center is represented by the first patch only.
LABELS: List[Label] = [(0, q, r) for q, r in AXIAL_POINTS]
LABELS += [(1, q, r) for q, r in AXIAL_POINTS if (q, r) != (0, 0)]
INDEX = {label: index for index, label in enumerate(LABELS)}
N = len(LABELS)


def patches(label: Label) -> Tuple[int, ...]:
    patch, q, r = label
    return (0, 1) if (q, r) == (0, 0) else (patch,)


def is_edge(left: Label, right: Label) -> bool:
    lp, lq, lr = left
    rp, rq, rr = right
    common_patch = bool(set(patches(left)) & set(patches(right)))
    if common_patch and axial_norm_sq((lq, lr), (rq, rr)) == 1:
        return True
    return (
        lp != rp
        and (lq, lr) == (rq, rr)
        and axial_norm_sq((lq, lr)) == 4
    )


def is_triple(a: Label, b: Label, c: Label) -> bool:
    if not (set(patches(a)) & set(patches(b)) & set(patches(c))):
        return False
    points = [(a[1], a[2]), (b[1], b[2]), (c[1], c[2])]
    return all(
        axial_norm_sq(points[i], points[j]) == 3
        for i, j in ((0, 1), (0, 2), (1, 2))
    )


EDGES = [
    (i, j)
    for i in range(N)
    for j in range(i + 1, N)
    if is_edge(LABELS[i], LABELS[j])
]
TRIPLES = [
    (i, j, k)
    for i in range(N)
    for j in range(i + 1, N)
    for k in range(j + 1, N)
    if is_triple(LABELS[i], LABELS[j], LABELS[k])
]

NEIGHBORS: List[List[int]] = [[] for _ in range(N)]
TRIPLE_PAIRS: List[List[Tuple[int, int]]] = [[] for _ in range(N)]
TRIPLES_AT: List[List[Tuple[int, int, int]]] = [[] for _ in range(N)]
TRIPLE_WITNESSES: List[
    List[Tuple[int, int, int, int, int, bool, int, int, bool]]
] = [[] for _ in range(N)]
for left, right in EDGES:
    NEIGHBORS[left].append(right)
    NEIGHBORS[right].append(left)
for a, b, c in TRIPLES:
    TRIPLE_PAIRS[a].append((b, c))
    TRIPLE_PAIRS[b].append((a, c))
    TRIPLE_PAIRS[c].append((a, b))
    for vertex in (a, b, c):
        TRIPLES_AT[vertex].append((a, b, c))

    common = (
        set(patches(LABELS[a]))
        & set(patches(LABELS[b]))
        & set(patches(LABELS[c]))
    )
    if len(common) != 1:
        raise RuntimeError((a, b, c, common))
    patch = next(iter(common))
    actual = [a, b, c]
    coords = [(LABELS[index][1], LABELS[index][2]) for index in actual]
    sum_q = sum(point[0] for point in coords)
    sum_r = sum(point[1] for point in coords)
    if sum_q % 3 or sum_r % 3:
        raise RuntimeError((a, b, c, coords))
    center_q, center_r = sum_q // 3, sum_r // 3
    positive = [
        (center_q + 1, center_r),
        (center_q, center_r - 1),
        (center_q - 1, center_r + 1),
    ]
    negative = [
        (center_q - 1, center_r),
        (center_q, center_r + 1),
        (center_q + 1, center_r - 1),
    ]
    if sorted(coords) == sorted(positive):
        expected, negated = positive, False
    elif sorted(coords) == sorted(negative):
        expected, negated = negative, True
    else:
        raise RuntimeError((a, b, c, coords, positive, negative))
    roles = [actual[coords.index(point)] for point in expected]
    for root, left, right in ((a, b, c), (b, a, c), (c, a, b)):
        TRIPLE_WITNESSES[root].append(
            (
                left,
                right,
                roles[0],
                roles[1],
                roles[2],
                bool(patch),
                center_q,
                center_r,
                negated,
            )
        )

NEGATION = [
    INDEX[(label[0], -label[1], -label[2])]
    if (label[1], label[2]) != (0, 0)
    else INDEX[(0, 0, 0)]
    for label in LABELS
]


@dataclass
class TreeNode:
    stem: List[Assignment]
    vertex: int
    children: List[Optional[int]]


@dataclass
class CaseLeaf:
    certificate: int


@dataclass
class CaseBranch:
    vertex: int
    children: List[Optional[object]]


def blocked(path: Dict[int, int], vertex: int, color: int) -> bool:
    if any(path.get(neighbor) == color for neighbor in NEIGHBORS[vertex]):
        return True
    return any(
        path.get(left) == color and path.get(right) == color
        for left, right in TRIPLE_PAIRS[vertex]
    )


def active_degree(path: Dict[int, int], vertex: int) -> int:
    edge_degree = sum(neighbor not in path for neighbor in NEIGHBORS[vertex])
    triple_degree = sum(
        any(other not in path for other in triple if other != vertex)
        for triple in TRIPLES_AT[vertex]
    )
    return edge_degree + triple_degree


def build_tree(roots: Sequence[Assignment]) -> List[TreeNode]:
    nodes: List[Optional[TreeNode]] = []

    def visit(path: Dict[int, int]) -> int:
        stem: List[Assignment] = []
        while True:
            dead: Optional[int] = None
            forced: Optional[Assignment] = None
            best: Optional[int] = None
            best_colors: Optional[List[int]] = None
            best_degree = -1

            for vertex in range(N):
                if vertex in path:
                    continue
                colors = [
                    color for color in range(4) if not blocked(path, vertex, color)
                ]
                if not colors:
                    dead = vertex
                    break
                if len(colors) == 1:
                    forced = (vertex, colors[0])
                    break
                degree = active_degree(path, vertex)
                if (
                    best is None
                    or len(colors) < len(best_colors or [])
                    or (
                        len(colors) == len(best_colors or [])
                        and degree > best_degree
                    )
                ):
                    best = vertex
                    best_colors = colors
                    best_degree = degree

            if dead is not None:
                index = len(nodes)
                nodes.append(TreeNode(stem, dead, [None] * 4))
                return index
            if forced is not None:
                path[forced[0]] = forced[1]
                stem.append(forced)
                continue
            if best is None or best_colors is None:
                raise RuntimeError("certificate search found a valid coloring")

            index = len(nodes)
            nodes.append(None)
            children: List[Optional[int]] = [None] * 4
            for color in best_colors:
                extended = dict(path)
                extended[best] = color
                children[color] = visit(extended)
            nodes[index] = TreeNode(stem, best, children)
            return index

    root = visit(dict(roots))
    if root != 0 or any(node is None for node in nodes):
        raise RuntimeError("malformed generated tree")
    return [node for node in nodes if node is not None]
