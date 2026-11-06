"""Hand-coded inverse rules for independently specified case-tree schedules."""
from itertools import zip_longest


def tree_type(node):
    if isinstance(node, tuple):
        return f"({tree_type(node[0])}) ∨ ({tree_type(node[1])})"
    return node[0]


def leaf(typ, projection="", *moves):
    return [typ, projection, moves]


def make_trace(tree, premises, target):
    goals = []
    edges = []
    shared = [f"h{i}:{typ}" for i, typ in enumerate(premises)]

    def state(context, conclusion):
        return ",".join(context) + " | " + conclusion

    def record(tactic):
        edges.append((tactic, goals.copy()))

    def add_node(node, depth):
        name = f"h{6-depth}"
        ctx = [*shared, f"{name}:{tree_type(node)}"]
        if isinstance(node, tuple):
            right, left = node[1], node[0]
            add_node(right, depth + 1)
            add_node(left, depth + 1)
            goals[:2] = [state(ctx, target)]
            record(f"cases {name} <;> rename_i h{5-depth}")
        else:
            typ, projection, moves = node
            immediate = moves[0][0] if moves else target
            goals.insert(0, state(ctx, immediate))
            record(f"exact {name}{projection}")
            for _, tactic, conclusion in moves:
                goals[0] = state(ctx, conclusion)
                record(tactic)

    add_node(tree, 0)
    conclusion = f"({tree_type(tree)}) → ({target})"
    goals[0] = state(shared, conclusion)
    record("intro h6")
    for index in reversed(range(len(premises))):
        conclusion = f"({premises[index]}) → ({conclusion})"
        goals[0] = state(shared[:index], conclusion)
        record(f"intro h{index}")
    return edges


def rule_rounds():
    a = ((leaf("P"), leaf("P ∧ Q", ".left")), leaf("R ∧ P", ".right"))
    b = (
        leaf("Q", "", ("Q", "left", "Q ∨ R")),
        (leaf("R", "", ("R", "right", "Q ∨ R")), leaf("P ∧ R", ".right", ("R", "right", "Q ∨ R"))),
    )
    c = ((leaf("P", "", ("P", "apply h0", "S")), leaf("Q", "", ("Q", "apply h1", "S"))), leaf("S"))
    d = ((leaf("P"), leaf("P ∧ Q", ".left")), (leaf("Q ∧ P", ".right"), leaf("(P ∧ R) ∧ S", ".left.left")))
    e = (
        (leaf("P", "", ("P", "left", "P ∨ Q")), leaf("Q", "", ("Q", "right", "P ∨ Q"))),
        (leaf("R ∧ P", ".right", ("P", "left", "P ∨ Q")), leaf("Q ∧ S", ".left", ("Q", "right", "P ∨ Q"))),
    )
    f = (
        (leaf("P", "", ("P", "apply h0", "R")), leaf("Q", "", ("Q", "apply h1", "R"))),
        (leaf("S", "", ("S", "apply h2", "R")), leaf("R")),
    )
    specs = [(a, [], "P"), (b, [], "Q ∨ R"), (c, ["P → S", "Q → S"], "S"),
             (d, [], "P"), (e, [], "P ∨ Q"), (f, ["P → R", "Q → R", "S → R"], "R")]
    traces = [make_trace(*spec) for spec in specs]
    return [{key: move for key, move in zip("abcdef", step) if move is not None}
            for step in zip_longest(*traces)]
