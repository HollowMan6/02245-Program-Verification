#!/usr/bin/env python3
TILE_EMPTY = 9
TILE_WALL = 8
TILE_0 = 0
TILE_1 = 1
TILE_2 = 2
TILE_3 = 3
TILE_4 = 4

CARDINAL = [(-1, 0), (0, 1), (1, 0), (0, -1)]

# Grids are defined as a list of lists of numbers. The outer layer corresponds
# to the rows of the puzzle, the inner layer corresponds to the columns. The
# numbers stored in the cells have the following meaning:
# - `9` (or `TILE_EMPTY`) indicates an empty tile.
# - `8` (or `TILE_WALL`) indicates a wall tile with no number on it.
# - `0` through `4` (or `TILE_n`) indicate a wall with the given number on it.
GRID_A = [
  [8,8,1],
  [8,9,9],
  [1,9,9],
]
GRID_B = [
  [8,9,9,9,8,9,9,8],
  [9,9,9,2,9,3,9,9],
  [9,8,9,9,9,9,9,9],
  [3,9,9,9,9,9,8,9],
  [9,8,9,9,9,9,9,8],
  [9,9,9,9,9,9,4,9],
  [9,9,8,9,8,9,9,9],
  [0,9,9,2,9,9,9,8],
]
GRID_C = [
  [9,9,8,8,1,9,9,0,9,9,9,9,9,1],
  [8,2,9,8,9,9,9,8,1,9,9,1,9,9],
  [9,1,9,9,9,9,9,9,9,9,9,8,8,8],
  [9,9,9,0,9,9,9,9,9,9,9,9,9,9],
  [9,9,9,9,9,8,9,9,1,9,9,9,0,2],
  [9,9,8,9,8,9,9,9,9,9,9,9,1,9],
  [9,9,9,9,1,9,1,8,0,9,1,9,9,2],
  [2,9,9,1,9,8,8,8,9,8,9,9,9,9],
  [9,8,9,9,9,9,9,9,9,8,9,8,9,9],
  [8,8,9,9,9,8,9,9,2,9,9,9,9,9],
  [9,9,9,9,9,9,9,9,9,9,1,9,9,9],
  [8,8,8,9,9,9,9,9,9,9,9,9,8,9],
  [9,9,2,9,9,8,1,9,9,9,2,9,8,8],
  [8,9,9,9,9,9,1,9,9,0,8,1,9,9],
]

GRID_D = [
  [8,9,9,9,8,9,8,8,9,9,8,9,9,9,9,9,9,0,9,9,9],
  [8,9,3,9,8,8,9,9,9,9,8,9,9,8,9,9,9,1,9,9,0],
  [9,9,9,1,9,9,9,2,1,9,9,8,3,9,9,0,9,9,9,9,8],
  [9,0,9,9,9,9,9,8,8,9,9,9,9,9,9,9,8,9,8,9,9],
  [9,9,9,9,1,9,8,9,8,2,9,8,8,0,9,1,9,9,9,8,9],
  [1,9,9,9,0,9,8,8,8,9,9,9,8,9,8,8,8,9,9,9,9],
  [8,8,9,9,9,9,9,9,9,9,9,9,9,9,9,8,9,9,0,9,9],
  [9,1,9,9,9,0,9,8,9,8,9,9,9,9,9,9,9,9,9,8,9],
  [9,9,9,0,9,9,9,9,1,8,9,9,9,3,9,9,9,3,9,9,9],
  [9,8,9,0,9,9,9,9,9,9,8,9,9,9,9,1,8,9,3,9,9],
  [9,9,9,9,9,9,9,8,8,9,9,8,8,8,8,9,8,9,9,9,1],
  [9,1,9,9,9,9,1,9,9,9,9,9,8,9,8,9,8,8,9,9,9],
  [9,9,9,9,9,9,9,9,3,9,9,8,9,8,9,8,9,9,9,9,9],
  [9,9,9,0,9,2,8,9,9,9,9,9,9,9,8,9,9,2,1,9,9],
  [8,8,9,9,9,9,9,8,9,9,9,9,3,9,9,9,8,8,9,9,1],
  [9,8,9,9,8,9,9,9,9,8,8,9,9,9,9,9,9,9,8,9,9],
  [9,9,8,2,9,8,9,3,0,9,9,8,9,9,9,3,9,9,8,0,9],
  [9,8,9,8,9,1,8,9,9,8,9,9,8,9,9,9,9,9,8,9,9],
  [2,8,9,9,9,9,8,9,9,8,9,2,9,9,9,9,9,9,9,9,9],
  [9,9,8,9,8,8,9,8,9,9,2,8,9,9,9,9,9,9,9,9,8],
  [8,9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,1,9,1,9,8],
]
GRID_E = [
  [8,8,9,9,9,9,8,9,3,9,9,8,1,9,9,8,9,1,9,9,9],
  [9,9,8,9,2,9,8,9,9,4,9,9,9,8,9,9,9,8,8,9,9],
  [9,9,0,8,9,9,1,9,8,9,8,8,8,8,1,9,9,9,9,9,9],
  [9,9,8,9,9,9,8,8,9,9,9,8,8,9,9,3,9,9,9,1,8],
  [1,9,9,9,2,9,9,9,9,0,9,9,8,8,9,9,9,9,9,1,9],
  [8,9,2,9,9,9,3,9,9,9,9,9,9,9,9,8,9,9,8,9,9],
  [8,8,9,1,8,8,9,2,9,9,9,9,2,9,8,9,1,9,9,9,9],
  [8,9,9,8,9,8,8,8,9,9,9,9,9,8,1,9,8,9,9,9,9],
  [9,8,8,9,9,9,9,9,9,9,9,9,9,9,9,9,9,8,2,9,9],
  [9,9,9,1,9,9,8,8,8,2,1,9,9,9,8,9,9,9,9,9,9],
  [2,9,9,9,9,9,9,8,9,9,1,9,8,8,9,9,2,9,8,9,8],
  [9,2,9,8,8,8,9,1,8,9,9,9,9,9,8,8,8,8,9,9,9],
  [8,9,9,9,2,8,9,9,9,9,9,9,9,8,8,1,9,8,9,9,9],
  [9,9,9,2,9,9,9,9,9,0,9,9,1,8,8,9,9,8,8,9,2],
  [0,9,9,9,2,9,9,9,8,0,9,8,9,9,9,9,9,9,9,9,9],
  [9,9,9,9,9,9,9,0,9,9,9,9,9,9,9,9,9,0,9,9,9],
  [9,9,9,9,9,9,9,0,8,9,9,9,2,9,1,9,2,8,9,9,8],
  [0,8,9,9,9,8,1,9,9,9,9,9,8,9,9,9,9,8,8,8,8],
  [8,8,9,9,9,8,9,1,9,9,9,9,8,9,9,8,9,8,9,9,8],
  [8,8,1,9,2,8,9,8,2,9,9,8,0,2,9,8,9,1,9,9,9],
  [8,8,9,9,9,9,9,8,9,2,9,9,9,9,8,9,9,8,9,8,9],
]
GRID_F = [
  [9,9,9,9,9,2,8,9,9,8,9,8,9,9,9,9,9,9,9,9,8],
  [8,9,8,9,9,9,3,9,9,9,9,9,9,9,9,2,9,9,1,8,8],
  [8,9,9,9,9,8,9,8,0,0,8,8,9,8,9,9,9,9,8,9,9],
  [2,9,9,9,9,9,8,8,9,9,9,8,9,0,9,9,9,9,1,9,8],
  [9,9,9,9,8,9,9,9,9,9,8,9,8,9,9,9,9,2,1,9,9],
  [9,1,9,8,9,9,0,9,9,8,9,9,8,8,9,9,9,9,8,9,9],
  [9,9,2,8,9,8,0,9,8,9,9,3,8,8,9,8,8,9,9,9,8],
  [9,9,9,8,9,9,8,8,8,9,3,9,9,8,9,9,9,1,9,9,9],
  [9,9,9,9,9,8,8,9,8,9,9,9,9,9,8,8,9,9,9,9,8],
  [9,9,9,0,8,9,9,8,9,9,9,9,1,9,9,9,9,9,8,8,9],
  [9,9,9,9,9,9,3,9,9,9,8,9,8,9,0,9,9,0,8,9,8],
  [9,8,8,9,8,8,9,8,9,2,9,9,9,9,9,9,8,9,9,8,9],
  [2,9,8,8,9,9,9,8,9,9,9,8,9,9,1,9,9,9,8,0,8],
  [9,9,8,9,9,0,9,9,9,9,8,9,3,8,8,9,9,1,9,9,9],
  [9,8,9,8,9,9,8,9,0,9,9,9,9,2,9,9,8,8,8,1,9],
  [8,9,9,9,9,9,9,9,8,1,8,9,9,9,9,9,9,9,8,9,9],
  [8,9,9,9,9,3,9,9,9,9,9,9,0,9,9,8,8,9,9,9,8],
  [9,9,1,9,9,9,9,0,0,8,9,9,9,9,8,9,9,9,9,9,9],
  [9,9,9,8,9,9,9,9,9,9,8,0,9,9,9,9,1,9,3,8,9],
  [8,8,9,2,9,8,9,9,8,1,9,9,9,9,8,9,8,8,9,2,9],
  [8,8,9,9,9,8,8,8,8,8,1,8,1,9,9,9,8,8,9,9,9],
]
GRID_G = [
  [8,9,2,9,9,0,9,9,9,9,9,8,8,9,2,8,9,9,9,9,9],
  [9,2,9,9,9,9,8,9,9,0,0,9,9,9,9,9,1,9,9,9,8],
  [9,9,9,1,8,8,9,9,9,2,8,9,9,9,2,9,9,2,9,9,9],
  [9,9,9,9,9,8,9,9,9,9,9,9,9,8,9,9,9,9,8,9,9],
  [9,9,9,9,9,3,9,9,9,9,9,9,9,8,1,9,8,8,1,9,9],
  [0,9,9,8,8,9,9,9,9,9,9,8,9,1,9,9,9,8,9,9,1],
  [9,9,9,9,9,9,1,9,9,9,1,9,9,9,9,2,1,8,9,9,9],
  [0,1,9,8,9,9,9,9,8,9,9,8,9,9,9,9,9,9,8,9,8],
  [9,9,9,9,8,9,8,9,9,9,9,9,9,9,9,9,9,9,8,9,9],
  [9,9,9,1,8,0,9,9,9,9,9,9,9,9,8,9,0,8,9,9,9],
  [9,8,9,9,9,8,8,8,0,9,8,8,9,9,0,9,9,9,8,9,9],
  [2,9,8,9,2,9,8,9,9,9,8,9,9,9,9,9,9,8,9,9,3],
  [9,3,9,9,9,9,9,8,8,9,8,0,9,9,9,1,1,0,8,9,9],
  [9,9,9,9,9,0,9,9,8,0,9,9,9,9,8,9,9,9,8,9,9],
  [9,9,9,2,9,9,8,8,9,9,2,9,9,8,8,9,9,9,9,8,8],
  [9,9,9,9,9,9,2,9,9,9,9,9,9,9,8,9,2,9,9,0,8],
  [8,9,9,8,9,3,9,8,8,9,9,8,9,9,8,9,9,9,9,9,9],
  [9,9,8,8,9,9,9,9,9,9,8,9,9,9,0,0,9,9,9,9,1],
  [3,9,1,9,8,9,8,9,8,8,9,8,1,9,9,9,9,9,9,1,8],
  [9,9,8,9,9,9,9,9,9,9,8,8,9,9,9,1,9,9,9,9,9],
  [9,1,9,9,8,9,9,8,9,9,9,9,2,9,9,9,9,9,9,2,9],
]

# Solutions are defined as lists of lists of booleans. A `True` (or `1`) cell
# indicates that a lightbulb is placed in that position.
SOLN_A = [
  [0,0,0],
  [0,0,1],
  [0,1,0],
]
SOLN_B = [
  [0,0,1,0,0,1,0,0],
  [0,1,0,0,1,0,1,0],
  [1,0,0,1,0,0,0,0],
  [0,1,0,0,0,0,0,1],
  [1,0,0,0,0,0,1,0],
  [0,0,0,0,0,1,0,1],
  [0,1,0,0,0,0,1,0],
  [0,0,1,0,1,0,0,0],
]
SOLN_C = [
  [0,1,0,0,0,1,0,0,0,0,0,1,0,0],
  [0,0,1,0,0,0,1,0,0,0,0,0,0,1],
  [0,0,0,0,0,0,0,0,1,0,0,0,0,0],
  [0,1,0,0,0,0,0,0,0,0,0,0,0,1],
  [0,0,0,0,1,0,0,1,0,0,1,0,0,0],
  [0,0,0,1,0,0,0,0,0,1,0,0,0,1],
  [1,0,0,0,0,1,0,0,0,0,0,1,0,0],
  [0,0,1,0,0,0,0,0,0,0,0,0,0,1],
  [1,0,0,0,0,0,0,0,1,0,1,0,0,0],
  [0,0,0,0,1,0,1,0,0,0,0,0,1,0],
  [0,0,0,0,0,0,0,0,1,0,0,0,0,0],
  [0,0,0,0,0,0,0,0,0,0,1,0,0,0],
  [0,1,0,1,0,0,0,1,0,0,0,1,0,0],
  [0,0,0,0,0,1,0,0,0,0,0,0,0,1],
]

def in_bounds(row, col, rows, cols):
  return 0 <= row < rows and 0 <= col < cols

# Given a grid (or a solution) returns a number of useful values and functions:
# - rows - the vertical dimension of the grid,
# - cols - the horizontal dimension of the grid,
# - in_grid - a function which, given a row and a column, returns `True` if the
#             given coordinates are within the grid, `False` otherwise.
# - adjacent - a function which, given a row and a column, returns a list of
#              coordinates that are directly adjacent to the given input and
#              also within the grid.
def grid_params(grid):
  rows = len(grid)
  cols = len(grid[0])
  assert all([ len(row) == cols for row in grid ])
  in_grid = lambda row, col: in_bounds(row, col, rows, cols)
  adjacent = lambda row, col: \
    [ (row + dr, col + dc) for dr, dc in CARDINAL if in_grid(row + dr, col + dc) ]
  return rows, cols, in_grid, adjacent

# Solution validator. Returns `True` if the solution is valid for the given
# grid, `False` otherwise. If `False` is returned, the problem with is printed
# to standard output.
def validate_solution(grid, solution):
  rows, cols, in_grid, adjacent = grid_params(grid)

  # Check: solution found.
  if not solution:
    print("no solution given")
    return False

  # Check: solution is well-formed.
  if (rows, cols) != grid_params(solution)[0:2]:
    print("solution/grid dimensions mismatch")
    return False

  # Check: all lightbulbs are placed on empty tiles.
  for row in range(rows):
    for col in range(cols):
      if solution[row][col] and grid[row][col] != TILE_EMPTY:
        print("lightbulb placed on wall", row, col)
        return False

  # Check: lightbulbs are placed according to the wall hints.
  for row in range(rows):
    for col in range(cols):
      if TILE_0 <= grid[row][col] <= TILE_4:
        placed = sum([ solution[ar][ac] for ar, ac in adjacent(row, col) ])
        if placed != grid[row][col]:
          print("incorrect number of lightbulbs placed", row, col)
          return False

  # Compute: which tiles are lit?
  lgrid = [ [ 0 for col in range(cols) ] for row in range(rows) ]
  for row in range(rows):
    for col in range(cols):
      if solution[row][col]:
        lgrid[row][col] += 1
        for dr, dc in CARDINAL:
          crow = row + dr
          ccol = col + dc
          while in_grid(crow, ccol) and grid[crow][ccol] == TILE_EMPTY:
            lgrid[crow][ccol] += 1
            crow += dr
            ccol += dc

  # Check: all empty tiles are lit.
  for row in range(rows):
    for col in range(cols):
      if grid[row][col] == TILE_EMPTY and lgrid[row][col] == 0:
        print("tile not lit", row, col)
        return False

  # Check: lightbulbs don't shine light on each other.
  for row in range(rows):
    for col in range(cols):
      if solution[row][col] and lgrid[row][col] > 1:
        print("lightbulb sees another lightbulb", row, col)
        return False

  # Otherwise, the solution is valid.
  return True

from z3 import *
# Grid solver.
def solve(grid):
    rows, cols, in_grid, adjacent = grid_params(grid)

    # Initialize Z3 solver
    solver = Solver()

    # Variables to represent the solution
    solution = [
        [Bool(f"light_{row}_{col}") for col in range(cols)] for row in range(rows)
    ]

    # Constraint: Lightbulbs can not be placed on wall or numbered tiles
    for row in range(rows):
        for col in range(cols):
            if grid[row][col] == TILE_WALL or (TILE_0 <= grid[row][col] <= TILE_4):
                solver.add(solution[row][col] == False)

    # Constraint: Lightbulbs should satisfy the adjacent wall hints
    for row in range(rows):
        for col in range(cols):
            if TILE_0 <= grid[row][col] <= TILE_4:
                solver.add(
                    Sum([If(solution[ar][ac], 1, 0) for ar, ac in adjacent(row, col)])
                    == grid[row][col]
                )

    for row in range(rows):
        for col in range(cols):
            if grid[row][col] == TILE_EMPTY:
                # Constraint: Lightbulbs should not shine on each other
                cond = [solution[row][col]]
                for dr, dc in CARDINAL:
                    crow = row + dr
                    ccol = col + dc
                    while in_grid(crow, ccol) and grid[crow][ccol] == TILE_EMPTY:
                        cond.append(solution[crow][ccol])
                        crow += dr
                        ccol += dc
                solver.add(Or(cond))

                # Check up and down
                vertical = [solution[row][col]]
                # Check left and right
                horizontal = [solution[row][col]]
                for d in [-1, 1]:
                    crow = row + d
                    ccol = col + d
                    while in_grid(crow, col) and grid[crow][col] == TILE_EMPTY:
                        vertical.append(solution[crow][col])
                        crow += d
                    while in_grid(row, ccol) and grid[row][ccol] == TILE_EMPTY:
                        horizontal.append(solution[row][ccol])
                        ccol += d
                solver.add(Sum([If(c, 1, 0) for c in vertical]) <= 1)
                solver.add(Sum([If(c, 1, 0) for c in horizontal]) <= 1)

    # Check if the solver can find a solution
    if solver.check() == sat:
        model = solver.model()
        result = [
            [is_true(model.evaluate(solution[r][c])) for c in range(cols)]
            for r in range(rows)
        ]
        return result
    return None

assert validate_solution(GRID_A, SOLN_A)
assert validate_solution(GRID_B, SOLN_B)
assert validate_solution(GRID_C, SOLN_C)

assert validate_solution(GRID_A, solve(GRID_A))
assert validate_solution(GRID_B, solve(GRID_B))
assert validate_solution(GRID_C, solve(GRID_C))
assert validate_solution(GRID_D, solve(GRID_D))
assert validate_solution(GRID_E, solve(GRID_E))
assert validate_solution(GRID_F, solve(GRID_F))
assert validate_solution(GRID_G, solve(GRID_G))
