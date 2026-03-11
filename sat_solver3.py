#!/usr/bin/env python3
"""SAT Solver — CDCL (Conflict-Driven Clause Learning) with watched literals."""

class CDCLSolver:
    def __init__(self, num_vars, clauses):
        self.n = num_vars
        self.clauses = [list(c) for c in clauses]
        self.assignment = {}; self.level = {}; self.reason = {}
        self.decision_level = 0; self.trail = []
        self.watches = {i: [] for i in range(-num_vars, num_vars+1) if i != 0}
        for i, clause in enumerate(self.clauses):
            if len(clause) >= 1: self.watches[-clause[0]].append(i)
            if len(clause) >= 2: self.watches[-clause[1]].append(i)

    def value(self, lit):
        var = abs(lit)
        if var not in self.assignment: return None
        return self.assignment[var] == (lit > 0)

    def assign(self, var, val, reason_clause=None):
        self.assignment[var] = val
        self.level[var] = self.decision_level
        self.reason[var] = reason_clause
        self.trail.append(var)

    def propagate(self):
        while True:
            unit = None
            for i, clause in enumerate(self.clauses):
                unset = []; satisfied = False
                for lit in clause:
                    v = self.value(lit)
                    if v is True: satisfied = True; break
                    if v is None: unset.append(lit)
                if satisfied: continue
                if not unset: return i  # conflict
                if len(unset) == 1:
                    unit = (abs(unset[0]), unset[0] > 0, i); break
            if unit is None: return -1
            self.assign(unit[0], unit[1], unit[2])

    def analyze(self, conflict_clause):
        if self.decision_level == 0: return None, -1
        clause = set(self.clauses[conflict_clause])
        while True:
            current_level_lits = [l for l in clause if self.level.get(abs(l)) == self.decision_level]
            if len(current_level_lits) <= 1: break
            for lit in reversed(self.trail):
                if lit in [abs(l) for l in current_level_lits] and self.reason.get(lit) is not None:
                    reason = set(self.clauses[self.reason[lit]])
                    resolvent = lit if lit in [abs(l) for l in clause if l > 0] else -lit
                    clause = (clause | reason) - {resolvent, -resolvent}
                    break
            else: break
        if not clause: return None, -1
        levels = [self.level.get(abs(l), 0) for l in clause]
        bt_level = sorted(set(levels))[-2] if len(set(levels)) > 1 else 0
        return list(clause), bt_level

    def backtrack(self, level):
        while self.trail and self.level.get(self.trail[-1], 0) > level:
            var = self.trail.pop()
            del self.assignment[var]; del self.level[var]; del self.reason[var]
        self.decision_level = level

    def solve(self):
        conflict = self.propagate()
        if conflict >= 0: return None
        while len(self.assignment) < self.n:
            # Decide
            var = next(v for v in range(1, self.n+1) if v not in self.assignment)
            self.decision_level += 1
            self.assign(var, True)
            while True:
                conflict = self.propagate()
                if conflict < 0: break
                learned, bt = self.analyze(conflict)
                if learned is None: return None
                self.clauses.append(learned)
                self.backtrack(bt)
        return {v: self.assignment[v] for v in range(1, self.n+1)}

if __name__ == "__main__":
    # (x1 ∨ x2) ∧ (¬x1 ∨ x3) ∧ (¬x2 ∨ ¬x3)
    result = CDCLSolver(3, [[1,2],[-1,3],[-2,-3]]).solve()
    print(f"SAT: {result}")
    # UNSAT: (x) ∧ (¬x)
    result2 = CDCLSolver(1, [[1],[-1]]).solve()
    print(f"UNSAT: {result2}")
    # Harder: pigeonhole-like
    result3 = CDCLSolver(4, [[1,2],[3,4],[-1,-3],[-1,-4],[-2,-3],[-2,-4]]).solve()
    print(f"Harder: {result3}")
