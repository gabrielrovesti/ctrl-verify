import sys
import pynusmv
from pynusmv_lower_interface.nusmv.parser import parser


# ---------------------------------------------------------------------------
# Token / type tables (from starter)
# ---------------------------------------------------------------------------

specTypes = {
    'LTLSPEC': parser.TOK_LTLSPEC, 'CONTEXT': parser.CONTEXT,
    'IMPLIES': parser.IMPLIES, 'IFF': parser.IFF,
    'OR': parser.OR, 'XOR': parser.XOR, 'XNOR': parser.XNOR,
    'AND': parser.AND, 'NOT': parser.NOT,
    'ATOM': parser.ATOM, 'NUMBER': parser.NUMBER, 'DOT': parser.DOT,
    'NEXT': parser.OP_NEXT, 'OP_GLOBAL': parser.OP_GLOBAL,
    'OP_FUTURE': parser.OP_FUTURE, 'UNTIL': parser.UNTIL,
    'EQUAL': parser.EQUAL, 'NOTEQUAL': parser.NOTEQUAL,
    'LT': parser.LT, 'GT': parser.GT, 'LE': parser.LE, 'GE': parser.GE,
    'TRUE': parser.TRUEEXP, 'FALSE': parser.FALSEEXP,
}

basicTypes = {
    parser.ATOM, parser.NUMBER, parser.TRUEEXP, parser.FALSEEXP,
    parser.DOT, parser.EQUAL, parser.NOTEQUAL,
    parser.LT, parser.GT, parser.LE, parser.GE,
}
booleanOp = {
    parser.AND, parser.OR, parser.XOR, parser.XNOR,
    parser.IMPLIES, parser.IFF,
}


# ---------------------------------------------------------------------------
# Helpers (from starter)
# ---------------------------------------------------------------------------

def spec_to_bdd(model, spec):
    """
    Given a propositional formula `spec` (no temporal operators),
    return the BDD of states satisfying it.
    """
    return pynusmv.mc.eval_simple_expression(model, str(spec))


def is_boolean_formula(spec):
    if spec.type in basicTypes:
        return True
    if spec.type == specTypes['NOT']:
        return is_boolean_formula(spec.car)
    if spec.type in booleanOp:
        return is_boolean_formula(spec.car) and is_boolean_formula(spec.cdr)
    return False


def parse(spec):
    """
    Check whether `spec` is a response formula  G(f → F g)  where f and g
    are boolean combinations of basic formulas.

    Returns (f_formula, g_formula) if it is, None otherwise.
    """
    if spec.type != specTypes['CONTEXT']:
        return None
    spec = spec.cdr                          # unwrap CONTEXT
    if spec.type != specTypes['OP_GLOBAL']:
        return None
    spec = spec.car                          # body of G
    if spec.type != specTypes['IMPLIES']:
        return None
    f_formula = spec.car
    if not is_boolean_formula(f_formula):
        return None
    g_formula = spec.cdr
    if g_formula.type != specTypes['OP_FUTURE']:
        return None
    g_formula = g_formula.car
    if not is_boolean_formula(g_formula):
        return None
    return f_formula, g_formula


# ---------------------------------------------------------------------------
# Core algorithm
# ---------------------------------------------------------------------------

def check_explain_response_spec(spec):
    """
    Verify a response formula  G(f → F g)  against the loaded SMV model.

    Algorithm
    ---------
    The formula is violated iff there exists an execution that visits a state
    where f holds and afterwards never reaches a g-state.  In a finite-state
    system this is equivalent to the existence of:

        • a reachable state s  with  s ⊨ f ∧ ¬g
        • an infinite path from s that stays in ¬g

    The set of states with *some* infinite ¬g-continuation is exactly  EG(¬g),
    computed as the greatest fixed-point:

        Z  =  gfp X .  ¬g  ∧  pre(X)

    Violation seeds:  bad_seeds = f_bdd ∧ Z  (f holds here AND a ¬g-forever
    path exists from here).

    We then run a forward BFS from init (unrestricted — the prefix may cross
    g-states) to detect whether any seed is reachable.

    Lasso counterexample
    --------------------
    • Prefix:  shortest path init → seed  (backward reconstruction over BFS
               layers, identical in structure to Part 1).
    • Loop:    from the seed, greedily follow successors inside Z until a state
               repeats (pigeonhole guarantees termination in ≤ |Z| steps).
               The last state in the loop tuple equals some earlier state,
               indicating the loop-back point.

    Returns
    -------
    None            if spec is not a response formula.
    (True,  None)   if the formula holds.
    (False, trace)  where trace is a lasso: a tuple of alternating state-dicts
                    and input-dicts whose last state is a repeat of an earlier
                    state.
    """
    parsed = parse(spec)
    if parsed is None:
        return None

    f_formula, g_formula = parsed
    model  = pynusmv.glob.prop_database().master.bddFsm
    F_bdd  = spec_to_bdd(model, f_formula)
    G_bdd  = spec_to_bdd(model, g_formula)
    not_G  = ~G_bdd

    # ---------- Step 1: compute EG(¬g) ----------
    # Greatest fixed-point:  Z = ¬g ∧ pre(Z),  starting from Z = ¬g
    # (valid because EG(¬g) ⊆ ¬g, so ¬g is above the GFP).
    Z = not_G
    while True:
        Z_new = not_G & model.pre(Z)
        if Z_new == Z:
            break
        Z = Z_new
    # Z  =  EG(¬g): states with some infinite path that never visits g

    # ---------- Step 2: violation seeds ----------
    bad_seeds = F_bdd & Z
    if bad_seeds.is_false():
        # No state satisfies f while also having a ¬g-forever continuation
        return True, None

    # ---------- Step 3: forward BFS to find a reachable seed ----------
    init      = model.init
    frontiers = [init]

    if not (init & bad_seeds).is_false():
        return False, _build_lasso(model, frontiers, bad_seeds, Z)

    reach    = init
    frontier = init

    while not frontier.is_false():
        new_frontier = model.post(frontier) & ~reach
        reach        = reach | new_frontier
        frontier     = new_frontier

        if frontier.is_false():
            break

        frontiers.append(frontier)

        if not (frontier & bad_seeds).is_false():
            return False, _build_lasso(model, frontiers, bad_seeds, Z)

    return True, None


# ---------------------------------------------------------------------------
# Counterexample reconstruction
# ---------------------------------------------------------------------------

def _build_prefix(model, frontiers, target):
    """
    Reconstruct the shortest path from init to a state in `target` BDD,
    using the stored BFS frontier layers.

    Returns (trace_tuple, entry_state_bdd) where trace_tuple ends at the
    picked target state and entry_state_bdd is that same state as a BDD
    (needed for the loop step).
    """
    k = len(frontiers) - 1

    s_current = model.pick_one_state(frontiers[k] & target)
    states = [s_current]
    inputs = []

    for i in range(k, 0, -1):
        prev_reach = frontiers[0]
        for j in range(1, i):
            prev_reach = prev_reach | frontiers[j]

        preds   = model.pre(s_current) & prev_reach
        s_prev  = model.pick_one_state(preds)
        inp_bdd = model.get_inputs_between_states(s_prev, s_current)
        one_inp = model.pick_one_inputs(inp_bdd)

        states.insert(0, s_prev)
        inputs.insert(0, one_inp)
        s_current = s_prev

    result = (states[0].get_str_values(),)
    for idx in range(len(inputs)):
        result += (inputs[idx].get_str_values(),
                   states[idx + 1].get_str_values())

    # states[-1] is the entry state (last in forward order)
    return result, states[-1]


def _build_loop(model, start_bdd, Z):
    """
    Starting from `start_bdd` ∈ Z = EG(¬g), follow successors within Z until
    a state is revisited.  Termination is guaranteed because Z is finite.

    Returns a tuple  (start_dict, inp0, s1, inp1, …, s_repeat_dict)
    where s_repeat_dict equals some earlier state in the tuple (the
    loop-back indicator).
    """
    elements   = [start_bdd.get_str_values()]
    seen_union = start_bdd   # BDD union of all visited single-state BDDs
    current    = start_bdd

    while True:
        # Every state in Z has at least one successor in Z (GFP property)
        succs  = model.post(current) & Z
        next_s = model.pick_one_state(succs)

        inp_bdd = model.get_inputs_between_states(current, next_s)
        one_inp = model.pick_one_inputs(inp_bdd)

        elements.append(one_inp.get_str_values())
        elements.append(next_s.get_str_values())

        # Loop closed when next_s is already in the visited set
        if not (next_s & seen_union).is_false():
            break

        seen_union = seen_union | next_s
        current    = next_s

    return tuple(elements)


def _build_lasso(model, frontiers, bad_seeds, Z):
    """
    Assemble the full lasso counterexample:
        prefix (init → entry_state)  +  loop (entry_state → … → repeated_state)

    The entry_state appears as the last element of the prefix and the first
    element of the loop; we splice them together without duplication.
    """
    prefix_tuple, entry_bdd = _build_prefix(model, frontiers, bad_seeds)
    loop_tuple              = _build_loop(model, entry_bdd, Z)
    # prefix ends with entry_dict; loop starts with the same entry_dict → skip it
    return prefix_tuple + loop_tuple[1:]


# ---------------------------------------------------------------------------
# Entry point
# ---------------------------------------------------------------------------

if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("Usage:", sys.argv[0], "filename.smv")
        sys.exit(1)

    pynusmv.init.init_nusmv()
    pynusmv.glob.load_from_file(sys.argv[1])
    pynusmv.glob.compute_model()

    type_ltl = pynusmv.prop.propTypes['LTL']
    for prop in pynusmv.glob.prop_database():
        spec = prop.expr
        print("Property:", spec)
        if prop.type != type_ltl:
            print("  Not an LTLSPEC, skipped.")
            continue
        res = check_explain_response_spec(spec)
        if res is None:
            print("  Not a response formula, skipped.")
        elif res[0]:
            print("  Formula is respected.")
        else:
            print("  Formula is NOT respected.")
            print("  Counterexample (lasso):")
            for i, elem in enumerate(res[1]):
                label = "  State" if i % 2 == 0 else "  Input"
                print(f"    {label}: {elem}")

    pynusmv.init.deinit_nusmv()
