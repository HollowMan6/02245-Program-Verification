import re
from z3 import *

def parse_expr(tree_str):
    # Extract kind value
    kind_match = re.search(r'kind: (\w+)', tree_str)
    kind = kind_match.group(1)
    
    span_match = re.search(r'span: Span {\s*start: (\d+),\s*end: (\d+),', tree_str)
    span = span_match.groups() if span_match else None
    
    if kind == "Binary":
        left_expr_str = re.search(r'Binary\((.*?),', tree_str, re.DOTALL).group(1)
        operator_str = re.search(r',\s*(\w+),', tree_str).group(1)
        right_expr_str = re.search(r',\s*\w+,\s*(Expr {.*?})', tree_str, re.DOTALL).group(1)
        
        left_expr, _ = parse_expr(left_expr_str)
        right_expr, _ = parse_expr(right_expr_str)
        
        if operator_str == 'Gt':
            return left_expr > right_expr, span
    elif kind == "Var":
        var_name = re.search(r'Var\(\s*"(\w+)"', tree_str).group(1)
        return Int(var_name), span
    elif kind == "Integer":
        value = re.search(r'Integer\(\s*"(-?\d+)"', tree_str).group(1)
        return int(value), span
    else:
        raise ValueError(f"Unknown kind: {kind}")

def evaluate_assert(tree_str):
    # Extract inner expression from Assert
    inner_expr_str = re.search(r'Assert\((.*)\)', tree_str, re.DOTALL).group(1)
    z3_expr, span = parse_expr(inner_expr_str)

    # Check satisfiability using Z3
    solver = Solver()
    solver.add(z3_expr)
    if solver.check() == sat:
        print("The formula is satisfiable.")
        print("Example model:", solver.model())
    else:
        print("The formula is unsatisfiable.")
        print(f"Span of failed assert: {span}")

# Read the file and split by "Assert"
with open('path_to_file.txt', 'r') as file:
    file_content = file.read()

# Split based on "Assert" but keep "Assert" in the splitted parts
assertions = ["Assert" + part for part in file_content.split("Assert")[1:]]

# Evaluate each assertion
for assertion in assertions:
    evaluate_assert(assertion)
