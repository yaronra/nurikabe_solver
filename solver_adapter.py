from nurikabe_solver_by_island import Solver, NoPossibleSolution, ProblemTooHard

def solve_nurikabe(rows: int, cols: int, clues):
    """
    Input
    -----
    rows, cols : int
    clues      : list[list[Optional[int]]]
                 - clue[i][j] is None or an island size (positive int)

    Output
    ------
    * list[list[int]] of same shape:
        1 = wall (black), 0 = island (white)
    OR
    message describing why no solution is found

    Raise an exception on internal errors.
    """
    clues_dict = {}
    for r, row in enumerate(clues):
        for c, clue in enumerate(row):
            if clue is not None:
                clues_dict[(r, c)] = clue
    try:
        solver = Solver(rows, cols, clues_dict, solution_island_cells=None, connection_cost_in_mip=True, verbose=True)
    except NoPossibleSolution:
        return "Puzzle has no solution"
    except ProblemTooHard:
        return "Solver couldn't solve puzzle"
    island_cells = solver.solve()
    solution = [
        [
            1 - ((r, c) in island_cells)
            for c in range(rows)
        ]
        for r in range(rows)
    ]
    return solution
