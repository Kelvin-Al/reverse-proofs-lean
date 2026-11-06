"""Eight fixed schedules over hand-coded inverse tactic rules."""
from itertools import zip_longest


def goal(context, target):
    bindings = ",".join(f"{name}:{typ}" for name, typ in context)
    return f"{bindings} | {target}"


class ReverseRules:
    def __init__(self):
        self.goals = []
        self.edges = []

    def record(self, tactic):
        self.edges.append((tactic, [goal(*entry) for entry in self.goals]))

    def exact(self, context, target, term):
        self.goals.insert(0, (context, target))
        self.record(f"exact {term}")

    def replace(self, tactic, context, target, count=1):
        self.goals[:count] = [(context, target)]
        self.record(tactic)

    def join(self):
        (context, left), (other, right) = self.goals[:2]
        assert context == other
        self.replace("constructor", context, f"({left}) ∧ ({right})", 2)

    def inject(self, side, other):
        context, target = self.goals[0]
        left, right = (target, other) if side == "left" else (other, target)
        self.replace(side, context, f"({left}) ∨ ({right})")

    def apply(self, name, conclusion):
        context, _ = self.goals[0]
        self.replace(f"apply {name}", context, conclusion)

    def merge_cases(self, hyp_name):
        (ctx_left, target), (ctx_right, other) = self.goals[:2]
        assert ctx_left[:-1] == ctx_right[:-1] and target == other
        (branch, left), (branch_right, right) = ctx_left[-1], ctx_right[-1]
        assert branch == branch_right
        context = [*ctx_left[:-1], (hyp_name, f"({left}) ∨ ({right})")]
        self.replace(f"cases {hyp_name} <;> rename_i {branch}", context, target, 2)

    def close(self):
        assert len(self.goals) == 1
        while self.goals[0][0]:
            context, target = self.goals[0]
            name, typ = context[-1]
            self.replace(f"intro {name}", context[:-1], f"({typ}) → ({target})")
        return self.edges


def rule_rounds():
    a, b, c, d, e, f, g, h = [ReverseRules() for _ in range(8)]
    a.exact([("h0", "P")], "P", "h0")

    pair = [("h0", "P ∧ Q")]
    b.exact(pair, "P", "h0.left")
    b.exact(pair, "Q", "h0.right")
    b.join()

    chain = [("h0", "P → Q"), ("h1", "Q → R"), ("h2", "P")]
    c.exact(chain, "P", "h2")
    c.apply("h0", "Q")
    c.apply("h1", "R")

    d.exact([("h0", "P ∧ (Q ∧ R)")], "R", "h0.right.right")
    d.inject("left", "S")

    e.exact([("h1", "Q")], "Q", "h1")
    e.inject("left", "P")
    e.exact([("h1", "P")], "P", "h1")
    e.inject("right", "Q")
    e.merge_cases("h0")

    f.exact([("h1", "P")], "P", "h1")
    f.exact([("h1", "P")], "P", "h1")
    f.merge_cases("h0")

    combined = [("h0", "Q → R"), ("h1", "P"), ("h2", "Q")]
    g.exact(combined, "Q", "h2")
    g.apply("h0", "R")
    g.exact(combined, "P", "h1")
    g.join()

    h.exact([("h0", "P → Q"), ("h1", "P")], "P", "h1")
    h.apply("h0", "Q")
    h.inject("right", "R")

    traces = [path.close() for path in (a, b, c, d, e, f, g, h)]
    return [{key: move for key, move in zip("abcdefgh", step) if move is not None}
            for step in zip_longest(*traces)]
