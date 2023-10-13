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
        elif operator_str == 'Eq':
            return left_expr == right_expr, span
    elif kind == "Var":
        var_name = re.search(r'Var\(\s*"(\w+)"', tree_str).group(1)
        return Int(var_name), span
    elif kind == "Integer":
        value = re.search(r'Integer\(\s*"(-?\d+)"', tree_str).group(1)
        return int(value), span
    else:
        raise ValueError(f"Unknown kind: {kind}")
        
    return None, None
    
def chain_implications(conditions):
    """Create a chained implication from a list of conditions."""
    if not conditions:
        return BoolVal(True)  # base case: return true for an empty list
    if len(conditions) == 1:
        return conditions[0]
    return Implies(conditions[0], chain_implications(conditions[1:]))

def evaluate_assert_and_assume(conditions):
    z3_conditions = []
    
    for condition in conditions:
        directive, tree_str = condition
        z3_expr, span = parse_expr(tree_str)
        if z3_expr is None:
            raise ValueError(f"Failed to parse expression: {tree_str}")
        
        z3_conditions.append(z3_expr)

    # Chain the implications
    formula = chain_implications(z3_conditions)
    
    negated_formula = Not(formula)

    print(negated_formula)
    
    solver = Solver()
    solver.add(negated_formula)
    if solver.check() == sat:
        print("The formula is satisfiable.")
        print("Example model:", solver.model())
        print("The program doesn't verify.")
    else:
        print("The formula is unsatisfiable.")
        print("The program verifies.")

# Read the file and split by "Assert" and "Assume"
with open('z3-input.txt', 'r') as file:
    file_content = file.read()

conditions = []
for part in re.split(r'(Assert|Assume)', file_content)[1:]:
    if part == 'Assert' or part == 'Assume':
        directive = part
    else:
        conditions.append((directive, part.strip()))

# Evaluate the conditions together
evaluate_assert_and_assume(conditions)
