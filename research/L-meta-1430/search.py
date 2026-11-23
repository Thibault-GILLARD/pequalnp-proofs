#!/usr/bin/env python3
"""Find minimum fan-in-two circuits for the ten tables of gap L-meta-1430.

For a nonconstant target, a minimum circuit can omit constants, duplicate wires,
and gates with no path to the output. Every remaining binary gate sees two
distinct earlier wires. A NOT gate sees one earlier wire.
"""
import argparse
from concurrent.futures import ProcessPoolExecutor
from itertools import combinations
import json
from pathlib import Path

from pysat.formula import IDPool
from pysat.solvers import Solver

INPUT_COUNT = 5
ROW_COUNT = 2 ** INPUT_COUNT
ALL_ROWS = (1 << ROW_COUNT) - 1
INPUT_TABLES = [
    sum(1 << row for row in range(ROW_COUNT) if (row >> variable) & 1)
    for variable in range(INPUT_COUNT)
]
TABLES = [
    0xEEE0E880, 0xAAAAAAA8, 0xE8E8E8A8, 0xEAA8AAA8, 0xEAA8E8A8,
    0xEAAAE888, 0xEAC8E8C8, 0xEAC8EAC0, 0xEAE8E888, 0xEAE8E8C0,
]


def synthesize(table, count, allow_not, solver_name):
    size = INPUT_COUNT + count
    if count == 0:
        return [] if table in INPUT_TABLES else None
    pool = IDPool()
    clauses = []
    wire_use = [[] for _ in range(size)]
    rows = [[pool.id(("wire", wire, row)) for row in range(ROW_COUNT)] for wire in range(size)]

    def exactly_one(literals):
        clauses.append(literals)
        clauses.extend([-a, -b] for a, b in combinations(literals, 2))

    for wire, inputs in enumerate(INPUT_TABLES):
        for row in range(ROW_COUNT):
            direction = 1 if (inputs >> row) & 1 else -1
            clauses.append([direction * rows[wire][row]])
    for row in range(ROW_COUNT):
        direction = 1 if (table >> row) & 1 else -1
        clauses.append([direction * rows[-1][row]])

    selected = []
    not_selectors = []
    operations = ("and", "or", "not") if allow_not else ("and", "or")
    for wire in range(INPUT_COUNT, size):
        op = {name: pool.id(("op", wire, name)) for name in operations}
        left = [pool.id(("left", wire, source)) for source in range(wire)]
        right = [pool.id(("right", wire, source)) for source in range(wire)]
        exactly_one(list(op.values()))
        exactly_one(left)
        exactly_one(right)
        selected.append((op, left, right))

        if allow_not:
            not_selectors.append(op["not"])
        for source in range(wire):
            wire_use[source].extend([left[source], right[source]])
            for other in range(source + 1):
                if allow_not and other == source:
                    clauses.extend([[-left[source], -right[other], op["not"]],
                                    [-left[source], -op["not"], right[source]]])
                else:
                    clauses.append([-left[source], -right[other]])

        for row in range(ROW_COUNT):
            lhs = pool.id(("lhs value", wire, row))
            rhs = pool.id(("rhs value", wire, row))
            result = rows[wire][row]
            for source in range(wire):
                value = rows[source][row]
                clauses.extend([
                    [-left[source], -value, lhs],
                    [-left[source], value, -lhs],
                    [-right[source], -value, rhs],
                    [-right[source], value, -rhs],
                ])
            clauses.extend([
                [-op["and"], -result, lhs],
                [-op["and"], -result, rhs],
                [-op["and"], result, -lhs, -rhs],
                [-op["or"], result, -lhs],
                [-op["or"], result, -rhs],
                [-op["or"], -result, lhs, rhs],
            ])
            if allow_not:
                clauses.extend([
                    [-op["not"], lhs, result],
                    [-op["not"], -lhs, -result],
                ])

    clauses.extend([-a, -b] for a, b in combinations(not_selectors, 2))
    clauses.extend(wire_use[wire] for wire in range(INPUT_COUNT, size - 1))
    for variable in range(INPUT_COUNT):
        bit = 1 << variable
        if any((table >> row) & 1 != (table >> (row ^ bit)) & 1 for row in range(ROW_COUNT)):
            clauses.append(wire_use[variable])

    with Solver(name=solver_name, bootstrap_with=clauses) as solver:
        if not solver.solve():
            return None
        model = {literal for literal in solver.get_model() if literal > 0}
    circuit = []
    for op, left, right in selected:
        operation = next(key for key, literal in op.items() if literal in model)
        a = next(index for index, literal in enumerate(left) if literal in model)
        b = next(index for index, literal in enumerate(right) if literal in model)
        circuit.append([operation, a] if operation == "not" else [operation, a, b])
    assert evaluate(circuit) == table
    return circuit


def evaluate(circuit):
    wires = INPUT_TABLES.copy()
    for gate in circuit:
        operation, a, *rest = gate
        if operation == "not":
            wires.append(wires[a] ^ ALL_ROWS)
        elif operation == "and":
            wires.append(wires[a] & wires[rest[0]])
        else:
            wires.append(wires[a] | wires[rest[0]])
    return wires[-1]


def search(parameters):
    table, limit, solver = parameters
    if table in INPUT_TABLES:
        return {"table": f"0x{table:08x}", "monotone_size": 0, "one_not_size": 0}
    for count in range(1, limit + 1):
        circuit = synthesize(table, count, False, solver)
        if circuit is not None:
            break
    else:
        return {"table": f"0x{table:08x}", "monotone_upper_bound_found": False}
    for smaller in range(1, count):
        one_not_circuit = synthesize(table, smaller, True, solver)
        if one_not_circuit is not None:
            break
    else:
        smaller = count
        one_not_circuit = circuit
    result = {
        "table": f"0x{table:08x}",
        "monotone_size": count,
        "monotone_circuit": circuit,
        "one_not_size": smaller,
        "one_not_circuit": one_not_circuit,
    }
    print(json.dumps(result), flush=True)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--limit", type=int, default=12)
    parser.add_argument("--jobs", type=int, default=4)
    parser.add_argument("--solver", default="cadical195")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    parameters = [(table, args.limit, args.solver) for table in TABLES]
    with ProcessPoolExecutor(max_workers=args.jobs) as pool:
        result = list(pool.map(search, parameters))
    args.output.write_text(json.dumps(result, indent=2) + "\n")


if __name__ == "__main__":
    main()
