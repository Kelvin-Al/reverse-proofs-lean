import re

PRECEDENCE = {"→": 1, "∨": 2, "∧": 3}


def parse_formula(source):
    tokens = iter(re.sub(r"\s", "", source))
    token = next(tokens, None)

    def read(minimum=1):
        nonlocal token
        if token in ("P", "Q", "R", "S"):
            left, token = token, next(tokens, None)
        elif token == "(":
            token = next(tokens, None)
            left = read()
            if token != ")":
                raise ValueError("unclosed parenthesis")
            token = next(tokens, None)
        else:
            raise ValueError("expected a propositional atom")
        while PRECEDENCE.get(token, 0) >= minimum:
            operator, token = token, next(tokens, None)
            left = (operator, left, read(PRECEDENCE[operator]))
        return left

    formula = read()
    if token is not None:
        raise ValueError("unexpected token after formula")
    return formula


def render(formula):
    if isinstance(formula, str):
        return formula
    operator, left, right = formula
    return f"({render(left)} {operator} {render(right)})"


def shape(formula, atoms):
    if isinstance(formula, str):
        return atoms(formula)
    operator, left, right = formula
    return (operator, shape(left, atoms), shape(right, atoms))


def size(formula):
    if isinstance(formula, str):
        return 0
    return 1 + size(formula[1]) + size(formula[2])
