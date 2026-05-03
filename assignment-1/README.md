## Part 1 — Symbolic Invariant Verification

We implemented `check_explain_inv_spec(spec)` using a **BDD-based forward reachability** algorithm, without delegating to NuSMV's built-in engines and without calling the forbidden `reachable_states` method.

**Algorithm.** The reachable state space is explored layer by layer via BFS over BDD-represented state sets:

- `frontiers[0]` = initial states (`model.init`)
- `frontiers[i]` = `post(frontiers[i−1]) ∖ (frontiers[0] ∪ … ∪ frontiers[i−1])`

At each layer we test `frontiers[i] ∩ ¬spec ≠ ∅`. As soon as this is non-empty, a violation has been found at depth `i` and we stop. If the BFS exhausts all reachable states without a violation, the invariant holds.

**Counterexample reconstruction.** When a violation is found at layer `k`, we reconstruct the shortest counterexample path by walking backwards through the stored frontier layers. At each step `i` (from `k` down to `1`), we compute:

```
pre(s_current) ∩ (frontiers[0] ∪ … ∪ frontiers[i−1])
```

and pick one predecessor. The valid input between each consecutive state pair is extracted via `get_inputs_between_states`. The result is a tuple of alternating state-dicts and input-dicts `(s₀, i₀, s₁, i₁, …, sₖ)`, starting and ending with a state, as required.

---

## Part 2 — Symbolic Response Property Verification

We implemented `check_explain_response_spec(spec)` for formulas of the form `G(f → Fg)`, where `f` and `g` are propositional (no temporal operators). Formulas not matching this shape are rejected by the existing `parse()` function and return `None`.

**Key reduction.** The formula `G(f → Fg)` is violated if and only if there exists a reachable state `s` such that:
- `s ⊨ f ∧ ¬g`
- there is an infinite execution from `s` that never visits a `g`-state

The set of states with *some* infinite `¬g`-avoiding continuation is exactly `EG(¬g)`, computed as a **greatest fixed-point**:

```
Z  =  gfp X .  ¬g  ∧  pre(X)
```

starting from `Z = ¬g` (valid since `EG(¬g) ⊆ ¬g`). The iteration is monotonically decreasing over a finite state space, so it always terminates. Violation seeds are then `f_bdd ∧ Z`.

**Reachability check.** A forward BFS from `model.init` — unrestricted, so the prefix path may cross `g`-states — checks whether any violation seed is reachable.

**Lasso counterexample construction.** The counterexample has two parts:

- **Prefix**: shortest path from an initial state to the reachable violation seed, reconstructed with the same backward predecessor-chasing technique as Part 1.
- **Loop**: from the seed state, we greedily follow successors within `Z`. Every state in `Z` has at least one successor in `Z` (guaranteed by the GFP property), so this never gets stuck. By the pigeonhole principle over the finite set `Z`, a state must repeat within at most `|Z|` steps. The moment a repeated state is detected the loop is closed.

The final trace is the prefix concatenated with the loop (the seed state — which is both the last element of the prefix and the first of the loop — appears only once). The last state in the tuple is a repeat of some earlier state, indicating the loop-back point as required by the specification.