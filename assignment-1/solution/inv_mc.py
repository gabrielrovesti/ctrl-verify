import pynusmv
import sys


# ---------------------------------------------------------------------------
# Helper
# ---------------------------------------------------------------------------

def spec_to_bdd(model, spec):
    """Return the BDD of states of `model` satisfying `spec`."""
    return pynusmv.mc.eval_ctl_spec(model, spec)


# ---------------------------------------------------------------------------
# Core algorithm
# ---------------------------------------------------------------------------

def check_explain_inv_spec(spec):
    """
    Symbolically verify that `spec` is an invariant of the loaded SMV model,
    i.e. every reachable state satisfies `spec`.

    Algorithm
    ---------
    Forward BFS over BDD-represented state sets (no call to reachable_states).

        frontiers[0]  = init
        frontiers[i]  = post(frontiers[i-1]) \\ (frontiers[0] ∪ … ∪ frontiers[i-1])

    At each step we test  frontiers[i] ∩ ¬spec ≠ ∅ .
    When a violation is found we reconstruct the shortest counterexample by
    walking backwards through the stored frontier layers, chasing one
    predecessor at a time.

    Returns
    -------
    (True,  None)   if the invariant holds, or
    (False, trace)  where trace is a tuple that alternates state-dicts and
                    input-dicts: (s0, i0, s1, i1, …, sk).
    """
    model = pynusmv.glob.prop_database().master.bddFsm
    P     = spec_to_bdd(model, spec)   # states that satisfy the invariant
    not_P = ~P                          # states that violate it

    init = model.init                  # BDD of initial states

    # ---------- check initial states first ----------
    frontiers = [init]
    if not (init & not_P).is_false():
        return False, _build_trace(model, frontiers, not_P)

    reach    = init
    frontier = init

    # ---------- BFS ----------
    while not frontier.is_false():
        new_frontier = model.post(frontier) & ~reach
        reach        = reach | new_frontier
        frontier     = new_frontier

        if frontier.is_false():
            break

        frontiers.append(frontier)

        if not (frontier & not_P).is_false():
            return False, _build_trace(model, frontiers, not_P)

    return True, None


# ---------------------------------------------------------------------------
# Counterexample reconstruction
# ---------------------------------------------------------------------------

def _build_trace(model, frontiers, not_P):
    """
    Reconstruct the shortest path from an initial state to a state in not_P,
    using the BFS frontier layers.

    Strategy: pick one bad state in frontiers[-1], then for each step i walk
    backwards and pick a predecessor that lies in the cumulative reach up to
    step i-1  (guaranteed to exist by the BFS invariant).

    Returns a tuple  (s0_dict, i0_dict, s1_dict, …, sk_dict).
    """
    k = len(frontiers) - 1

    # Pick one violating state in the deepest frontier
    s_current = model.pick_one_state(frontiers[k] & not_P)

    states_bdd = [s_current]   # State objects (BDDs), newest first → will reverse
    inputs_bdd = []

    for i in range(k, 0, -1):
        # Cumulative reach up to step i-1
        prev_reach = frontiers[0]
        for j in range(1, i):
            prev_reach = prev_reach | frontiers[j]

        # One predecessor of s_current that was reached before step i
        preds   = model.pre(s_current) & prev_reach
        s_prev  = model.pick_one_state(preds)

        # One valid input that drives s_prev → s_current
        inp_bdd = model.get_inputs_between_states(s_prev, s_current)
        one_inp = model.pick_one_inputs(inp_bdd)

        states_bdd.insert(0, s_prev)
        inputs_bdd.insert(0, one_inp)
        s_current = s_prev

    # Assemble alternating (state, input, state, …, state) tuple
    result = (states_bdd[0].get_str_values(),)
    for idx in range(len(inputs_bdd)):
        result += (inputs_bdd[idx].get_str_values(),
                   states_bdd[idx + 1].get_str_values())
    return result


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

    invtype = pynusmv.prop.propTypes['Invariant']
    for prop in pynusmv.glob.prop_database():
        spec = prop.expr
        if prop.type == invtype:
            print("Property", spec, "is an INVARSPEC.")
            res, trace = check_explain_inv_spec(spec)
            if res:
                print("  Invariant is respected")
            else:
                print("  Invariant is NOT respected")
                print("  Counterexample:")
                for i, elem in enumerate(trace):
                    label = "  State" if i % 2 == 0 else "  Input"
                    print(f"    {label}: {elem}")
        else:
            print("Property", spec, "is not an INVARSPEC, skipped.")

    pynusmv.init.deinit_nusmv()
