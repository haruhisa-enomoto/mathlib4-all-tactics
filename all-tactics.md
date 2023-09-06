# #find
Defined in: `Mathlib.Tactic.Find.«tactic#find_»`


# (
Defined in: `Lean.Parser.Tactic.paren`

`(tacs)` executes a list of tactics in sequence, without requiring that
the goal be closed at the end like `· tacs`. Like `by` itself, the tactics
can be either separated by newlines or `;`.

# _
Defined in: `Std.Tactic.tactic_`

`_` in tactic position acts like the `done` tactic: it fails and gives the list
of goals if there are any. It is useful as a placeholder after starting a tactic block
such as `by _` to make it syntactically correct and show the current goal.

# abel
Defined in: `Mathlib.Tactic.Abel.abel_term`

Unsupported legacy syntax from mathlib3, which allowed passing additional terms to `abel`.

# abel
Defined in: `Mathlib.Tactic.Abel.abel`

Tactic for evaluating expressions in abelian groups.

* `abel!` will use a more aggressive reducibility setting to determine equality of atoms.
* `abel1` fails if the target is not an equality.

For example:
```
example [AddCommMonoid α] (a b : α) : a + (b + a) = a + a + b := by abel
example [AddCommGroup α] (a : α) : (3 : ℤ) • a = a + (2 : ℤ) • a := by abel
```

# abel!
Defined in: `Mathlib.Tactic.Abel.abel!_term`

Unsupported legacy syntax from mathlib3, which allowed passing additional terms to `abel!`.

# abel!
Defined in: `Mathlib.Tactic.Abel.tacticAbel!`

Tactic for evaluating expressions in abelian groups.

* `abel!` will use a more aggressive reducibility setting to determine equality of atoms.
* `abel1` fails if the target is not an equality.

For example:
```
example [AddCommMonoid α] (a b : α) : a + (b + a) = a + a + b := by abel
example [AddCommGroup α] (a : α) : (3 : ℤ) • a = a + (2 : ℤ) • a := by abel
```

# abel1
Defined in: `Mathlib.Tactic.Abel.abel1`

Tactic for solving equations in the language of
*additive*, commutative monoids and groups.
This version of `abel` fails if the target is not an equality
that is provable by the axioms of commutative monoids/groups.

`abel1!` will use a more aggressive reducibility setting to identify atoms.
This can prove goals that `abel` cannot, but is more expensive.

# abel1!
Defined in: `Mathlib.Tactic.Abel.abel1!`

Tactic for solving equations in the language of
*additive*, commutative monoids and groups.
This version of `abel` fails if the target is not an equality
that is provable by the axioms of commutative monoids/groups.

`abel1!` will use a more aggressive reducibility setting to identify atoms.
This can prove goals that `abel` cannot, but is more expensive.

# abel_nf
Defined in: `Mathlib.Tactic.Abel.abelNF`

Simplification tactic for expressions in the language of abelian groups,
which rewrites all group expressions into a normal form.
* `abel_nf!` will use a more aggressive reducibility setting to identify atoms.
* `abel_nf (config := cfg)` allows for additional configuration:
  * `red`: the reducibility setting (overridden by `!`)
  * `recursive`: if true, `abel_nf` will also recurse into atoms
* `abel_nf` works as both a tactic and a conv tactic.
  In tactic mode, `abel_nf at h` can be used to rewrite in a hypothesis.

# abel_nf!
Defined in: `Mathlib.Tactic.Abel.tacticAbel_nf!__`

Simplification tactic for expressions in the language of abelian groups,
which rewrites all group expressions into a normal form.
* `abel_nf!` will use a more aggressive reducibility setting to identify atoms.
* `abel_nf (config := cfg)` allows for additional configuration:
  * `red`: the reducibility setting (overridden by `!`)
  * `recursive`: if true, `abel_nf` will also recurse into atoms
* `abel_nf` works as both a tactic and a conv tactic.
  In tactic mode, `abel_nf at h` can be used to rewrite in a hypothesis.

# absurd
Defined in: `Std.Tactic.tacticAbsurd_`

Given a proof `h` of `p`, `absurd h` changes the goal to `⊢ ¬ p`.
If `p` is a negation `¬q` then the goal is changed to `⊢ q` instead.

# ac_change
Defined in: `Mathlib.Tactic.acChange`

`ac_change g using n` is `convert_to g using n` followed by `ac_rfl`. It is useful for
rearranging/reassociating e.g. sums:
```lean
example (a b c d e f g N : ℕ) : (a + b) + (c + d) + (e + f) + g ≤ N := by
  ac_change a + d + e + f + c + g + b ≤ _
  -- ⊢ a + d + e + f + c + g + b ≤ N
```

# ac_rfl
Defined in: `Lean.Parser.Tactic.acRfl`

`ac_rfl` proves equalities up to application of an associative and commutative operator.
```
instance : IsAssociative (α := Nat) (.+.) := ⟨Nat.add_assoc⟩
instance : IsCommutative (α := Nat) (.+.) := ⟨Nat.add_comm⟩

example (a b c d : Nat) : a + b + c + d = d + (b + c) + a := by ac_rfl
```

# admit
Defined in: `Lean.Parser.Tactic.tacticAdmit`

`admit` is a shorthand for `exact sorry`.

# aesop
Defined in: `Aesop.Frontend.Parser.aesopTactic`

`aesop <clause>*` tries to solve the current goal by applying a set of rules
registered with the `@[aesop]` attribute. See [its
README](https://github.com/JLimperg/aesop#readme) for a tutorial and a
reference.

The variant `aesop?` prints the proof it found as a `Try this` suggestion.

Clauses can be used to customise the behaviour of an Aesop call. Available
clauses are:

- `(add <phase> <priority> <builder> <rule>)` adds a rule. `<phase>` is
  `unsafe`, `safe` or `norm`. `<priority>` is a percentage for unsafe rules and
  an integer for safe and norm rules. `<rule>` is the name of a declaration or
  local hypothesis. `<builder>` is the rule builder used to turn `<rule>` into
  an Aesop rule. Example: `(add unsafe 50% apply Or.inl)`.
- `(erase <rule>)` disables a globally registered Aesop rule. Example: `(erase
  Aesop.BuiltinRules.assumption)`.
- `(rule_sets [<ruleset>,*])` enables or disables named sets of rules for this
  Aesop call. Example: `(rule_sets [-builtin, MyRuleSet])`.
- `(options { <opt> := <value> })` adjusts Aesop's search options. See
  `Aesop.Options`.
- `(simp_options { <opt> := <value> })` adjusts options for Aesop's built-in
  `simp` rule. See `Aesop.SimpConfig`.

# aesop?
Defined in: `Aesop.Frontend.Parser.aesopTactic?`

`aesop <clause>*` tries to solve the current goal by applying a set of rules
registered with the `@[aesop]` attribute. See [its
README](https://github.com/JLimperg/aesop#readme) for a tutorial and a
reference.

The variant `aesop?` prints the proof it found as a `Try this` suggestion.

Clauses can be used to customise the behaviour of an Aesop call. Available
clauses are:

- `(add <phase> <priority> <builder> <rule>)` adds a rule. `<phase>` is
  `unsafe`, `safe` or `norm`. `<priority>` is a percentage for unsafe rules and
  an integer for safe and norm rules. `<rule>` is the name of a declaration or
  local hypothesis. `<builder>` is the rule builder used to turn `<rule>` into
  an Aesop rule. Example: `(add unsafe 50% apply Or.inl)`.
- `(erase <rule>)` disables a globally registered Aesop rule. Example: `(erase
  Aesop.BuiltinRules.assumption)`.
- `(rule_sets [<ruleset>,*])` enables or disables named sets of rules for this
  Aesop call. Example: `(rule_sets [-builtin, MyRuleSet])`.
- `(options { <opt> := <value> })` adjusts Aesop's search options. See
  `Aesop.Options`.
- `(simp_options { <opt> := <value> })` adjusts options for Aesop's built-in
  `simp` rule. See `Aesop.SimpConfig`.

# aesop_cases
Defined in: `Aesop.tacticAesop_cases_`


# aesop_cat
Defined in: `CategoryTheory.aesop_cat`

A thin wrapper for `aesop` which adds the `CategoryTheory` rule set and
allows `aesop` to look through semireducible definitions when calling `intros`.
This tactic fails when it is unable to solve the goal, making it suitable for
use in auto-params.

# aesop_cat?
Defined in: `CategoryTheory.aesop_cat?`

We also use `aesop_cat?` to pass along a `Try this` suggestion when using `aesop_cat`

# aesop_cat_nonterminal
Defined in: `CategoryTheory.aesop_cat_nonterminal`

A variant of `aesop_cat` which does not fail when it is unable to solve the
goal. Use this only for exploration! Nonterminal `aesop` is even worse than
nonterminal `simp`.

# aesop_destruct_products
Defined in: `Aesop.BuiltinRules.tacticAesop_destruct_products`


# aesop_split_hyps
Defined in: `Aesop.BuiltinRules.tacticAesop_split_hyps`


# aesop_subst
Defined in: `Aesop.BuiltinRules.«tacticAesop_subst[_,,`
»]

# aesop_subst
Defined in: `Aesop.BuiltinRules.tacticAesop_subst_`


# aesop_unfold
Defined in: `Aesop.«tacticAesop_unfold[_,,`
»]

# all_goals
Defined in: `Lean.Parser.Tactic.allGoals`

`all_goals tac` runs `tac` on each goal, concatenating the resulting goals, if any.

# any_goals
Defined in: `Lean.Parser.Tactic.anyGoals`

`any_goals tac` applies the tactic `tac` to every goal, and succeeds if at
least one application succeeds.

# apply
Defined in: `Lean.Parser.Tactic.apply`

`apply e` tries to match the current goal against the conclusion of `e`'s type.
If it succeeds, then the tactic returns as many subgoals as the number of premises that
have not been fixed by type inference or type class resolution.
Non-dependent premises are added before dependent ones.

The `apply` tactic uses higher-order pattern matching, type class resolution,
and first-order unification with dependent types.

# apply
Defined in: `Mathlib.Tactic.applyWith`

`apply (config := cfg) e` is like `apply e` but allows you to provide a configuration
`cfg : ApplyConfig` to pass to the underlying apply operation.

# apply?
Defined in: `Mathlib.Tactic.LibrarySearch.apply?'`


# apply_assumption
Defined in: `Mathlib.Tactic.SolveByElim.applyAssumptionSyntax`

`apply_assumption` looks for an assumption of the form `... → ∀ _, ... → head`
where `head` matches the current goal.

You can specify additional rules to apply using `apply_assumption [...]`.
By default `apply_assumption` will also try `rfl`, `trivial`, `congrFun`, and `congrArg`.
If you don't want these, or don't want to use all hypotheses, use `apply_assumption only [...]`.
You can use `apply_assumption [-h]` to omit a local hypothesis.
You can use `apply_assumption using [a₁, ...]` to use all lemmas which have been labelled
with the attributes `aᵢ` (these attributes must be created using `register_label_attr`).

`apply_assumption` will use consequences of local hypotheses obtained via `symm`.

If `apply_assumption` fails, it will call `exfalso` and try again.
Thus if there is an assumption of the form `P → ¬ Q`, the new tactic state
will have two goals, `P` and `Q`.

You can pass a further configuration via the syntax `apply_rules (config := {...}) lemmas`.
The options supported are the same as for `solve_by_elim` (and include all the options for `apply`).

# apply_ext_lemma
Defined in: `Std.Tactic.Ext.tacticApply_ext_lemma`

Apply a single extensionality lemma to the current goal.

# apply_fun
Defined in: `Mathlib.Tactic.applyFun`

Apply a function to an equality or inequality in either a local hypothesis or the goal.

* If we have `h : a = b`, then `apply_fun f at h` will replace this with `h : f a = f b`.
* If we have `h : a ≤ b`, then `apply_fun f at h` will replace this with `h : f a ≤ f b`,
  and create a subsidiary goal `Monotone f`.
  `apply_fun` will automatically attempt to discharge this subsidiary goal using `mono`,
  or an explicit solution can be provided with `apply_fun f at h using P`, where `P : Monotone f`.
* If we have `h : a < b`, then `apply_fun f at h` will replace this with `h : f a < f b`,
  and create a subsidiary goal `StrictMono f` and behaves as in the previous case.
* If we have `h : a ≠ b`, then `apply_fun f at h` will replace this with `h : f a ≠ f b`,
  and create a subsidiary goal `Injective f` and behaves as in the previous two cases.
* If the goal is `a ≠ b`, `apply_fun f` will replace this with `f a ≠ f b`.
* If the goal is `a = b`, `apply_fun f` will replace this with `f a = f b`,
  and create a subsidiary goal `injective f`.
  `apply_fun` will automatically attempt to discharge this subsidiary goal using local hypotheses,
  or if `f` is actually an `Equiv`,
  or an explicit solution can be provided with `apply_fun f using P`, where `P : Injective f`.
* If the goal is `a ≤ b` (or similarly for `a < b`), and `f` is actually an `OrderIso`,
  `apply_fun f` will replace the goal with `f a ≤ f b`.
  If `f` is anything else (e.g. just a function, or an `Equiv`), `apply_fun` will fail.


Typical usage is:
```lean
open Function

example (X Y Z : Type) (f : X → Y) (g : Y → Z) (H : Injective <| g ∘ f) :
    Injective f := by
  intros x x' h
  apply_fun g at h
  exact H h
```

The function `f` is handled similarly to how it would be handled by `refine` in that `f` can contain
placeholders. Named placeholders (like `?a` or `?_`) will produce new goals.

# apply_mod_cast
Defined in: `Tactic.NormCast.tacticApply_mod_cast_`

Normalize the goal and the given expression, then apply the expression to the goal.

# apply_rules
Defined in: `Mathlib.Tactic.SolveByElim.applyRulesSyntax`

`apply_rules [l₁, l₂, ...]` tries to solve the main goal by iteratively
applying the list of lemmas `[l₁, l₂, ...]` or by applying a local hypothesis.
If `apply` generates new goals, `apply_rules` iteratively tries to solve those goals.
You can use `apply_rules [-h]` to omit a local hypothesis.

`apply_rules` will also use `rfl`, `trivial`, `congrFun` and `congrArg`.
These can be disabled, as can local hypotheses, by using `apply_rules only [...]`.

You can use `apply_rules using [a₁, ...]` to use all lemmas which have been labelled
with the attributes `aᵢ` (these attributes must be created using `register_label_attr`).

You can pass a further configuration via the syntax `apply_rules (config := {...})`.
The options supported are the same as for `solve_by_elim` (and include all the options for `apply`).

`apply_rules` will try calling `symm` on hypotheses and `exfalso` on the goal as needed.
This can be disabled with `apply_rules (config := {symm := false, exfalso := false})`.

You can bound the iteration depth using the syntax `apply_rules (config := {maxDepth := n})`.

Unlike `solve_by_elim`, `apply_rules` does not perform backtracking, and greedily applies
a lemma from the list until it gets stuck.

# array_get_dec
Defined in: `Array.tacticArray_get_dec`

This tactic, added to the `decreasing_trivial` toolbox, proves that
`sizeOf arr[i] < sizeOf arr`, which is useful for well founded recursions
over a nested inductive like `inductive T | mk : Array T → T`.

# assumption
Defined in: `Lean.Parser.Tactic.assumption`

`assumption` tries to solve the main goal using a hypothesis of compatible type, or else fails.
Note also the `‹t›` term notation, which is a shorthand for `show t by assumption`.

# assumption'
Defined in: `Mathlib.Tactic.tacticAssumption'`

Try calling `assumption` on all goals; succeeds if it closes at least one goal.

# assumption_mod_cast
Defined in: `Tactic.NormCast.tacticAssumption_mod_cast`

`assumption_mod_cast` runs `norm_cast` on the goal. For each local hypothesis `h`, it also
normalizes `h` and tries to use that to close the goal.

# aux_group₁
Defined in: `Mathlib.Tactic.Group.aux_group₁`

Auxiliary tactic for the `group` tactic. Calls the simplifier only.

# aux_group₂
Defined in: `Mathlib.Tactic.Group.aux_group₂`

Auxiliary tactic for the `group` tactic. Calls `ring_nf` to normalize exponents.

# bddDefault
Defined in: `tacticBddDefault`

Sets are automatically bounded or cobounded in complete lattices. To use the same statements
in complete and conditionally complete lattices but let automation fill automatically the
boundedness proofs in complete lattices, we use the tactic `bddDefault` in the statements,
in the form `(hA : BddAbove A := by bddDefault)`.

# beta_reduce
Defined in: `Mathlib.Tactic.betaReduceStx`

`beta_reduce at loc` completely beta reduces the given location.
This also exists as a `conv`-mode tactic.

This means that whenever there is an applied lambda expression such as
`(fun x => f x) y` then the argument is substituted into the lambda expression
yielding an expression such as `f y`.

# bicategory_coherence
Defined in: `Mathlib.Tactic.BicategoryCoherence.tacticBicategory_coherence`

Coherence tactic for bicategories.
Use `pure_coherence` instead, which is a frontend to this one.

# bitwise_assoc_tac
Defined in: `Nat.tacticBitwise_assoc_tac`

Proving associativity of bitwise operations in general essentially boils down to a huge case
distinction, so it is shorter to use this tactic instead of proving it in the general case.

# by_cases
Defined in: `Classical.«tacticBy_cases_:_»`

`by_cases (h :)? p` splits the main goal into two cases, assuming `h : p` in the first branch, and `h : ¬ p` in the second branch.

# by_cases
Defined in: `Mathlib.Tactic.tacticBy_cases_`

`by_cases p` makes a case distinction on `p`,
resulting in two subgoals `h : p ⊢` and `h : ¬ p ⊢`.

# by_contra
Defined in: `Std.Tactic.byContra`

`by_contra h` proves `⊢ p` by contradiction,
introducing a hypothesis `h : ¬p` and proving `False`.
* If `p` is a negation `¬q`, `h : q` will be introduced instead of `¬¬q`.
* If `p` is decidable, it uses `Decidable.byContradiction` instead of `Classical.byContradiction`.
* If `h` is omitted, the introduced variable `_: ¬p` will be anonymous.

# by_contra'
Defined in: `byContra'`

If the target of the main goal is a proposition `p`,
`by_contra'` reduces the goal to proving `False` using the additional hypothesis `this : ¬ p`.
`by_contra' h` can be used to name the hypothesis `h : ¬ p`.
The hypothesis `¬ p` will be negation normalized using `push_neg`.
For instance, `¬ a < b` will be changed to `b ≤ a`.
`by_contra' h : q` will normalize negations in `¬ p`, normalize negations in `q`,
and then check that the two normalized forms are equal.
The resulting hypothesis is the pre-normalized form, `q`.
If the name `h` is not explicitly provided, then `this` will be used as name.
This tactic uses classical reasoning.
It is a variant on the tactic `by_contra`.
Examples:
```lean
example : 1 < 2 := by
  by_contra' h
  -- h : 2 ≤ 1 ⊢ False

example : 1 < 2 := by
  by_contra' h : ¬ 1 < 2
  -- h : ¬ 1 < 2 ⊢ False
```

# calc
Defined in: `calcTactic`

Step-wise reasoning over transitive relations.
```
calc
  a = b := pab
  b = c := pbc
  ...
  y = z := pyz
```
proves `a = z` from the given step-wise proofs. `=` can be replaced with any
relation implementing the typeclass `Trans`. Instead of repeating the right-
hand sides, subsequent left-hand sides can be replaced with `_`.
```
calc
  a = b := pab
  _ = c := pbc
  ...
  _ = z := pyz
```
It is also possible to write the *first* relation as `<lhs>\n  _ = <rhs> :=
<proof>`. This is useful for aligning relation symbols:
```
calc abc
  _ = bce := pabce
  _ = cef := pbcef
  ...
  _ = xyz := pwxyz
```

`calc` has term mode and tactic mode variants. This is the tactic mode variant,
which supports an additional feature: it works even if the goal is `a = z'`
for some other `z'`; in this case it will not close the goal but will instead
leave a subgoal proving `z = z'`.

See [Theorem Proving in Lean 4][tpil4] for more information.

[tpil4]: https://leanprover.github.io/theorem_proving_in_lean4/quantifiers_and_equality.html#calculational-proofs

# cancel_denoms
Defined in: `tacticCancel_denoms_`


# cancel_denoms
Defined in: `cancelDenoms`

`cancel_denoms` attempts to remove numerals from the denominators of fractions.
It works on propositions that are field-valued inequalities.

```lean
variable [LinearOrderedField α] (a b c : α)

example (h : a / 5 + b / 4 < c) : 4*a + 5*b < 20*c := by
  cancel_denoms at h
  exact h

example (h : a > 0) : a / 5 > 0 := by
  cancel_denoms
  exact h
```

# case
Defined in: `Lean.Parser.Tactic.case`

* `case tag => tac` focuses on the goal with case name `tag` and solves it using `tac`,
  or else fails.
* `case tag x₁ ... xₙ => tac` additionally renames the `n` most recent hypotheses
  with inaccessible names to the given names.
* `case tag₁ | tag₂ => tac` is equivalent to `(case tag₁ => tac); (case tag₂ => tac)`.

# case'
Defined in: `Lean.Parser.Tactic.case'`

`case'` is similar to the `case tag => tac` tactic, but does not ensure the goal
has been solved after applying `tac`, nor admits the goal if `tac` failed.
Recall that `case` closes the goal using `sorry` when `tac` fails, and
the tactic execution is not interrupted.

# cases
Defined in: `Lean.Parser.Tactic.cases`

Assuming `x` is a variable in the local context with an inductive type,
`cases x` splits the main goal, producing one goal for each constructor of the
inductive type, in which the target is replaced by a general instance of that constructor.
If the type of an element in the local context depends on `x`,
that element is reverted and reintroduced afterward,
so that the case split affects that hypothesis as well.
`cases` detects unreachable cases and closes them automatically.

For example, given `n : Nat` and a goal with a hypothesis `h : P n` and target `Q n`,
`cases n` produces one goal with hypothesis `h : P 0` and target `Q 0`,
and one goal with hypothesis `h : P (Nat.succ a)` and target `Q (Nat.succ a)`.
Here the name `a` is chosen automatically and is not accessible.
You can use `with` to provide the variables names for each constructor.
- `cases e`, where `e` is an expression instead of a variable, generalizes `e` in the goal,
  and then cases on the resulting variable.
- Given `as : List α`, `cases as with | nil => tac₁ | cons a as' => tac₂`,
  uses tactic `tac₁` for the `nil` case, and `tac₂` for the `cons` case,
  and `a` and `as'` are used as names for the new variables introduced.
- `cases h : e`, where `e` is a variable or an expression,
  performs cases on `e` as above, but also adds a hypothesis `h : e = ...` to each hypothesis,
  where `...` is the constructor instance for that particular case.

# cases'
Defined in: `Mathlib.Tactic.cases'`


# cases_type
Defined in: `Mathlib.Tactic.casesType`

* `cases_type I` applies the `cases` tactic to a hypothesis `h : (I ...)`
* `cases_type I_1 ... I_n` applies the `cases` tactic to a hypothesis
  `h : (I_1 ...)` or ... or `h : (I_n ...)`
* `cases_type* I` is shorthand for `· repeat cases_type I`
* `cases_type! I` only applies `cases` if the number of resulting subgoals is <= 1.

Example: The following tactic destructs all conjunctions and disjunctions in the current goal.
```
cases_type* Or And
```

# cases_type!
Defined in: `Mathlib.Tactic.casesType!`

* `cases_type I` applies the `cases` tactic to a hypothesis `h : (I ...)`
* `cases_type I_1 ... I_n` applies the `cases` tactic to a hypothesis
  `h : (I_1 ...)` or ... or `h : (I_n ...)`
* `cases_type* I` is shorthand for `· repeat cases_type I`
* `cases_type! I` only applies `cases` if the number of resulting subgoals is <= 1.

Example: The following tactic destructs all conjunctions and disjunctions in the current goal.
```
cases_type* Or And
```

# casesm
Defined in: `Mathlib.Tactic.casesM`

* `casesm p` applies the `cases` tactic to a hypothesis `h : type`
  if `type` matches the pattern `p`.
* `casesm p_1, ..., p_n` applies the `cases` tactic to a hypothesis `h : type`
  if `type` matches one of the given patterns.
* `casesm* p` is a more efficient and compact version of `· repeat casesm p`.
  It is more efficient because the pattern is compiled once.

Example: The following tactic destructs all conjunctions and disjunctions in the current context.
```
casesm* _ ∨ _, _ ∧ _
```

# change
Defined in: `Lean.Parser.Tactic.change`

* `change tgt'` will change the goal from `tgt` to `tgt'`,
  assuming these are definitionally equal.
* `change t' at h` will change hypothesis `h : t` to have type `t'`, assuming
  assuming `t` and `t'` are definitionally equal.

# change
Defined in: `Lean.Parser.Tactic.changeWith`

* `change a with b` will change occurrences of `a` to `b` in the goal,
  assuming `a` and `b` are are definitionally equal.
* `change a with b at h` similarly changes `a` to `b` in the type of hypothesis `h`.

# change?
Defined in: `change?`

`change? term` unifies `term` with the current goal, then suggests explicit `change` syntax
that uses the resulting unified term.

If `term` is not present, `change?` suggests the current goal itself. This is useful after tactics
which transform the goal while maintaining definitional equality, such as `dsimp`; those preceding
tactic calls can then be deleted.
```lean
example : (fun x : Nat => x) 0 = 1 := by
  change? 0 = _  -- `Try this: change 0 = 1`
```

# checkpoint
Defined in: `Lean.Parser.Tactic.checkpoint`

`checkpoint tac` acts the same as `tac`, but it caches the input and output of `tac`,
and if the file is re-elaborated and the input matches, the tactic is not re-run and
its effects are reapplied to the state. This is useful for improving responsiveness
when working on a long tactic proof, by wrapping expensive tactics with `checkpoint`.

See the `save` tactic, which may be more convenient to use.

(TODO: do this automatically and transparently so that users don't have to use
this combinator explicitly.)

# choose
Defined in: `Mathlib.Tactic.Choose.choose`

* `choose a b h h' using hyp` takes a hypothesis `hyp` of the form
  `∀ (x : X) (y : Y), ∃ (a : A) (b : B), P x y a b ∧ Q x y a b`
  for some `P Q : X → Y → A → B → Prop` and outputs
  into context a function `a : X → Y → A`, `b : X → Y → B` and two assumptions:
  `h : ∀ (x : X) (y : Y), P x y (a x y) (b x y)` and
  `h' : ∀ (x : X) (y : Y), Q x y (a x y) (b x y)`. It also works with dependent versions.

* `choose! a b h h' using hyp` does the same, except that it will remove dependency of
  the functions on propositional arguments if possible. For example if `Y` is a proposition
  and `A` and `B` are nonempty in the above example then we will instead get
  `a : X → A`, `b : X → B`, and the assumptions
  `h : ∀ (x : X) (y : Y), P x y (a x) (b x)` and
  `h' : ∀ (x : X) (y : Y), Q x y (a x) (b x)`.

The `using hyp` part can be omitted,
which will effectively cause `choose` to start with an `intro hyp`.

Examples:

```
example (h : ∀ n m : ℕ, ∃ i j, m = n + i ∨ m + j = n) : True := by
  choose i j h using h
  guard_hyp i : ℕ → ℕ → ℕ
  guard_hyp j : ℕ → ℕ → ℕ
  guard_hyp h : ∀ (n m : ℕ), m = n + i n m ∨ m + j n m = n
  trivial
```

```
example (h : ∀ i : ℕ, i < 7 → ∃ j, i < j ∧ j < i+i) : True := by
  choose! f h h' using h
  guard_hyp f : ℕ → ℕ
  guard_hyp h : ∀ (i : ℕ), i < 7 → i < f i
  guard_hyp h' : ∀ (i : ℕ), i < 7 → f i < i + i
  trivial
```

# choose!
Defined in: `Mathlib.Tactic.Choose.tacticChoose!___Using_`

* `choose a b h h' using hyp` takes a hypothesis `hyp` of the form
  `∀ (x : X) (y : Y), ∃ (a : A) (b : B), P x y a b ∧ Q x y a b`
  for some `P Q : X → Y → A → B → Prop` and outputs
  into context a function `a : X → Y → A`, `b : X → Y → B` and two assumptions:
  `h : ∀ (x : X) (y : Y), P x y (a x y) (b x y)` and
  `h' : ∀ (x : X) (y : Y), Q x y (a x y) (b x y)`. It also works with dependent versions.

* `choose! a b h h' using hyp` does the same, except that it will remove dependency of
  the functions on propositional arguments if possible. For example if `Y` is a proposition
  and `A` and `B` are nonempty in the above example then we will instead get
  `a : X → A`, `b : X → B`, and the assumptions
  `h : ∀ (x : X) (y : Y), P x y (a x) (b x)` and
  `h' : ∀ (x : X) (y : Y), Q x y (a x) (b x)`.

The `using hyp` part can be omitted,
which will effectively cause `choose` to start with an `intro hyp`.

Examples:

```
example (h : ∀ n m : ℕ, ∃ i j, m = n + i ∨ m + j = n) : True := by
  choose i j h using h
  guard_hyp i : ℕ → ℕ → ℕ
  guard_hyp j : ℕ → ℕ → ℕ
  guard_hyp h : ∀ (n m : ℕ), m = n + i n m ∨ m + j n m = n
  trivial
```

```
example (h : ∀ i : ℕ, i < 7 → ∃ j, i < j ∧ j < i+i) : True := by
  choose! f h h' using h
  guard_hyp f : ℕ → ℕ
  guard_hyp h : ∀ (i : ℕ), i < 7 → i < f i
  guard_hyp h' : ∀ (i : ℕ), i < 7 → f i < i + i
  trivial
```

# classical
Defined in: `Mathlib.Tactic.tacticClassical_`

`classical tacs` runs `tacs` in a scope where `Classical.propDecidable` is a low priority
local instance. It differs from `classical!` in that `classical!` uses a local variable,
which has high priority:
```
noncomputable def foo : Bool := by
  classical!
  have := ∀ p, decide p -- uses the classical instance
  exact decide (0 < 1) -- uses the classical instance even though `0 < 1` is decidable

def bar : Bool := by
  classical
  have := ∀ p, decide p -- uses the classical instance
  exact decide (0 < 1) -- uses the decidable instance
```
Note that (unlike lean 3) `classical` is a scoping tactic - it adds the instance only within the
scope of the tactic.

# classical!
Defined in: `Mathlib.Tactic.classical!`

`classical!` adds a proof of `Classical.propDecidable` as a local variable, which makes it
available for instance search and effectively makes all propositions decidable.
```
noncomputable def foo : Bool := by
  classical!
  have := ∀ p, decide p -- uses the classical instance
  exact decide (0 < 1) -- uses the classical instance even though `0 < 1` is decidable
```
Consider using `classical` instead if you want to use the decidable instance when available.

# clear
Defined in: `Lean.Elab.Tactic.clearExcept`

Clears all hypotheses it can besides those provided

# clear
Defined in: `Lean.Parser.Tactic.clear`

`clear x...` removes the given hypotheses, or fails if there are remaining
references to a hypothesis.

# clear!
Defined in: `Mathlib.Tactic.clear!`

A variant of `clear` which clears not only the given hypotheses but also any other hypotheses
depending on them

# clear_
Defined in: `Mathlib.Tactic.clear_`

Clear all hypotheses starting with `_`, like `_match` and `_let_match`.

# clear_aux_decl
Defined in: `Mathlib.Tactic.clearAuxDecl`

This tactic clears all auxiliary declarations from the context.

# clear_value
Defined in: `Mathlib.Tactic.clearValue`

`clear_value n₁ n₂ ...` clears the bodies of the local definitions `n₁, n₂ ...`, changing them
into regular hypotheses. A hypothesis `n : α := t` is changed to `n : α`.

The order of `n₁ n₂ ...` does not matter, and values will be cleared in reverse order of
where they appear in the context.

# coherence
Defined in: `Mathlib.Tactic.Coherence.coherence`

Use the coherence theorem for monoidal categories to solve equations in a monoidal equation,
where the two sides only differ by replacing strings of monoidal structural morphisms
(that is, associators, unitors, and identities)
with different strings of structural morphisms with the same source and target.

That is, `coherence` can handle goals of the form
`a ≫ f ≫ b ≫ g ≫ c = a' ≫ f ≫ b' ≫ g ≫ c'`
where `a = a'`, `b = b'`, and `c = c'` can be proved using `pure_coherence`.

(If you have very large equations on which `coherence` is unexpectedly failing,
you may need to increase the typeclass search depth,
using e.g. `set_option synthInstance.maxSize 500`.)

# compareOfLessAndEq_rfl
Defined in: `tacticCompareOfLessAndEq_rfl`

This attempts to prove that a given instance of `compare` is equal to `compareOfLessAndEq` by
introducing the arguments and trying the following approaches in order:

1. seeing if `rfl` works
2. seeing if the `compare` at hand is nonetheless essentially `compareOfLessAndEq`, but, because of
implicit arguments, requires us to unfold the defs and split the `if`s in the definition of
`compareOfLessAndEq`
3. seeing if we can split by cases on the arguments, then see if the defs work themselves out
  (useful when `compare` is defined via a `match` statement, as it is for `Bool`)

# compute_degree
Defined in: `Mathlib.Tactic.ComputeDegree.computeDegree`

`compute_degree` is a tactic to solve goals of the form
*  `natDegree f = d`,
*  `degree f = d`,
*  `natDegree f ≤ d`,
*  `degree f ≤ d`,
*  `coeff f d = r`, if `d` is the degree of `f`.

The tactic may leave goals of the form `d' = d` `d' ≤ d`, or `r ≠ 0`, where `d'` in `ℕ` or
`WithBot ℕ` is the tactic's guess of the degree, and `r` is the coefficient's guess of the
leading coefficient of `f`.

`compute_degree` applies `norm_num` to the left-hand side of all side goals, trying to clos them.

The variant `compute_degree!` first applies `compute_degree`.
Then it uses `norm_num` on all the whole remaining goals and tries `assumption`.

# compute_degree!
Defined in: `Mathlib.Tactic.ComputeDegree.tacticCompute_degree!`

`compute_degree` is a tactic to solve goals of the form
*  `natDegree f = d`,
*  `degree f = d`,
*  `natDegree f ≤ d`,
*  `degree f ≤ d`,
*  `coeff f d = r`, if `d` is the degree of `f`.

The tactic may leave goals of the form `d' = d` `d' ≤ d`, or `r ≠ 0`, where `d'` in `ℕ` or
`WithBot ℕ` is the tactic's guess of the degree, and `r` is the coefficient's guess of the
leading coefficient of `f`.

`compute_degree` applies `norm_num` to the left-hand side of all side goals, trying to clos them.

The variant `compute_degree!` first applies `compute_degree`.
Then it uses `norm_num` on all the whole remaining goals and tries `assumption`.

# congr
Defined in: `Std.Tactic.congrConfigWith`

Apply congruence (recursively) to goals of the form `⊢ f as = f bs` and `⊢ HEq (f as) (f bs)`.
* `congr n` controls the depth of the recursive applications.
  This is useful when `congr` is too aggressive in breaking down the goal.
  For example, given `⊢ f (g (x + y)) = f (g (y + x))`,
  `congr` produces the goals `⊢ x = y` and `⊢ y = x`,
  while `congr 2` produces the intended `⊢ x + y = y + x`.
* If, at any point, a subgoal matches a hypothesis then the subgoal will be closed.
* You can use `congr with p (: n)?` to call `ext p (: n)?` to all subgoals generated by `congr`.
  For example, if the goal is `⊢ f '' s = g '' s` then `congr with x` generates the goal
  `x : α ⊢ f x = g x`.

# congr
Defined in: `Std.Tactic.congrConfig`

Apply congruence (recursively) to goals of the form `⊢ f as = f bs` and `⊢ HEq (f as) (f bs)`.
The optional parameter is the depth of the recursive applications.
This is useful when `congr` is too aggressive in breaking down the goal.
For example, given `⊢ f (g (x + y)) = f (g (y + x))`,
`congr` produces the goals `⊢ x = y` and `⊢ y = x`,
while `congr 2` produces the intended `⊢ x + y = y + x`.

# congr
Defined in: `Lean.Parser.Tactic.congr`

Apply congruence (recursively) to goals of the form `⊢ f as = f bs` and `⊢ HEq (f as) (f bs)`.
The optional parameter is the depth of the recursive applications.
This is useful when `congr` is too aggressive in breaking down the goal.
For example, given `⊢ f (g (x + y)) = f (g (y + x))`,
`congr` produces the goals `⊢ x = y` and `⊢ y = x`,
while `congr 2` produces the intended `⊢ x + y = y + x`.

# congr!
Defined in: `Congr!.congr!`

Equates pieces of the left-hand side of a goal to corresponding pieces of the right-hand side by
recursively applying congruence lemmas. For example, with `⊢ f as = g bs` we could get
two goals `⊢ f = g` and `⊢ as = bs`.

Syntax:
```
congr!
congr! n
congr! with x y z
congr! n with x y z
```
Here, `n` is a natural number and `x`, `y`, `z` are `rintro` patterns (like `h`, `rfl`, `⟨x, y⟩`,
`_`, `-`, `(h | h)`, etc.).

The `congr!` tactic is similar to `congr` but is more insistent in trying to equate left-hand sides
to right-hand sides of goals. Here is a list of things it can try:

- If `R` in `⊢ R x y` is a reflexive relation, it will convert the goal to `⊢ x = y` if possible.
  The list of reflexive relations is maintained using the `@[refl]` attribute.
  As a special case, `⊢ p ↔ q` is converted to `⊢ p = q` during congruence processing and then
  returned to `⊢ p ↔ q` form at the end.

- If there is a user congruence lemma associated to the goal (for instance, a `@[congr]`-tagged
  lemma applying to `⊢ List.map f xs = List.map g ys`), then it will use that.

- It uses a congruence lemma generator at least as capable as the one used by `congr` and `simp`.
  If there is a subexpression that can be rewritten by `simp`, then `congr!` should be able
  to generate an equality for it.

- It can do congruences of pi types using lemmas like `implies_congr` and `pi_congr`.

- Before applying congruences, it will run the `intros` tactic automatically.
  The introduced variables can be given names using a `with` clause.
  This helps when congruence lemmas provide additional assumptions in hypotheses.

- When there is an equality between functions, so long as at least one is obviously a lambda, we
  apply `funext` or `Function.hfunext`, which allows for congruence of lambda bodies.

- It can try to close goals using a few strategies, including checking
  definitional equality, trying to apply `Subsingleton.elim` or `proof_irrel_heq`, and using the
  `assumption` tactic.

The optional parameter is the depth of the recursive applications.
This is useful when `congr!` is too aggressive in breaking down the goal.
For example, given `⊢ f (g (x + y)) = f (g (y + x))`,
`congr!` produces the goals `⊢ x = y` and `⊢ y = x`,
while `congr! 2` produces the intended `⊢ x + y = y + x`.

The `congr!` tactic also takes a configuration option, for example
```lean
congr! (config := {transparency := .default}) 2
```
This overrides the default, which is to apply congruence lemmas at reducible transparency.

The `congr!` tactic is aggressive with equating two sides of everything. There is a predefined
configuration that uses a different strategy:
Try
```lean
congr! (config := .unfoldSameFun)
```
This only allows congruences between functions applications of definitionally equal functions,
and it applies congruence lemmas at default transparency (rather than just reducible).
This is somewhat like `congr`.

See `Congr!.Config` for all options.

# congrm
Defined in: `Mathlib.Tactic.congrM`

`congrm e` is a tactic for proving goals of the form `lhs = rhs`, `lhs ↔ rhs`, `HEq lhs rhs`,
or `R lhs rhs` when `R` is a reflexive relation.
The expression `e` is a pattern containing placeholders `?_`,
and this pattern is matched against `lhs` and `rhs` simultaneously.
These placeholders generate new goals that state that corresponding subexpressions
in `lhs` and `rhs` are equal.
If the placeholders have names, such as `?m`, then the new goals are given tags with those names.

Examples:
```lean
example {a b c d : ℕ} :
    Nat.pred a.succ * (d + (c + a.pred)) = Nat.pred b.succ * (b + (c + d.pred)) := by
  congrm Nat.pred (Nat.succ ?h1) * (?h2 + ?h3)
  /-  Goals left:
  case h1 ⊢ a = b
  case h2 ⊢ d = b
  case h3 ⊢ c + a.pred = c + d.pred
  -/
  sorry
  sorry
  sorry

example {a b : ℕ} (h : a = b) : (fun y : ℕ => ∀ z, a + a = z) = (fun x => ∀ z, b + a = z) := by
  congrm fun x => ∀ w, ?_ + a = w
  -- ⊢ a = b
  exact h
```

The `congrm` command is a convenient frontend to `congr(...)` congruence quotations.
If the goal is an equality, `congrm e` is equivalent to `refine congr(e')` where `e'` is
built from `e` by replacing each placeholder `?m` by `$(?m)`.
The pattern `e` is allowed to contain `$(...)` expressions to immediately substitute
equality proofs into the congruence, just like for congruence quotations.

# constructor
Defined in: `Lean.Parser.Tactic.constructor`

If the main goal's target type is an inductive type, `constructor` solves it with
the first matching constructor, or else fails.

# constructorm
Defined in: `Mathlib.Tactic.constructorM`

* `constructorm p_1, ..., p_n` applies the `constructor` tactic to the main goal
  if `type` matches one of the given patterns.
* `constructorm* p` is a more efficient and compact version of `· repeat constructorm p`.
  It is more efficient because the pattern is compiled once.

Example: The following tactic proves any theorem like `True ∧ (True ∨ True)` consisting of
and/or/true:
```
constructorm* _ ∨ _, _ ∧ _, True
```

# continuity
Defined in: `tacticContinuity`

The tactic `continuity` solves goals of the form `Continuous f` by applying lemmas tagged with the
`continuity` user attribute.

# continuity?
Defined in: `tacticContinuity?`

The tactic `continuity` solves goals of the form `Continuous f` by applying lemmas tagged with the
`continuity` user attribute.

# contradiction
Defined in: `Lean.Parser.Tactic.contradiction`

`contradiction` closes the main goal if its hypotheses are "trivially contradictory".
- Inductive type/family with no applicable constructors
```lean
example (h : False) : p := by contradiction
```
- Injectivity of constructors
```lean
example (h : none = some true) : p := by contradiction  --
```
- Decidable false proposition
```lean
example (h : 2 + 2 = 3) : p := by contradiction
```
- Contradictory hypotheses
```lean
example (h : p) (h' : ¬ p) : q := by contradiction
```
- Other simple contradictions such as
```lean
example (x : Nat) (h : x ≠ x) : p := by contradiction
```

# contrapose
Defined in: `Mathlib.Tactic.Contrapose.contrapose`

Transforms the goal into its contrapositive.
* `contrapose`     turns a goal `P → Q` into `¬ Q → ¬ P`
* `contrapose h`   first reverts the local assumption `h`, and then uses `contrapose` and `intro h`
* `contrapose h with new_h` uses the name `new_h` for the introduced hypothesis

# contrapose!
Defined in: `Mathlib.Tactic.Contrapose.contrapose!`

Transforms the goal into its contrapositive and uses pushes negations inside `P` and `Q`.
Usage matches `contrapose`

# conv
Defined in: `Lean.Parser.Tactic.Conv.conv`

`conv => ...` allows the user to perform targeted rewriting on a goal or hypothesis,
by focusing on particular subexpressions.

See <https://leanprover.github.io/theorem_proving_in_lean4/conv.html> for more details.

Basic forms:
* `conv => cs` will rewrite the goal with conv tactics `cs`.
* `conv at h => cs` will rewrite hypothesis `h`.
* `conv in pat => cs` will rewrite the first subexpression matching `pat` (see `pattern`).

# conv'
Defined in: `Lean.Parser.Tactic.Conv.convTactic`

Executes the given conv block without converting regular goal into a `conv` goal.

# conv_lhs
Defined in: `Mathlib.Tactic.Conv.convLHS`


# conv_rhs
Defined in: `Mathlib.Tactic.Conv.convRHS`


# convert
Defined in: `Mathlib.Tactic.convert`

The `exact e` and `refine e` tactics require a term `e` whose type is
definitionally equal to the goal. `convert e` is similar to `refine e`,
but the type of `e` is not required to exactly match the
goal. Instead, new goals are created for differences between the type
of `e` and the goal using the same strategies as the `congr!` tactic.
For example, in the proof state

```lean
n : ℕ,
e : Prime (2 * n + 1)
⊢ Prime (n + n + 1)
```

the tactic `convert e using 2` will change the goal to

```lean
⊢ n + n = 2 * n
```

In this example, the new goal can be solved using `ring`.

The `using 2` indicates it should iterate the congruence algorithm up to two times,
where `convert e` would use an unrestricted number of iterations and lead to two
impossible goals: `⊢ HAdd.hAdd = HMul.hMul` and `⊢ n = 2`.

A variant configuration is `convert (config := .unfoldSameFun) e`, which only equates function
applications for the same function (while doing so at the higher `default` transparency).
This gives the same goal of `⊢ n + n = 2 * n` without needing `using 2`.

The `convert` tactic applies congruence lemmas eagerly before reducing,
therefore it can fail in cases where `exact` succeeds:
```lean
def p (n : ℕ) := True
example (h : p 0) : p 1 := by exact h -- succeeds
example (h : p 0) : p 1 := by convert h -- fails, with leftover goal `1 = 0`
```
Limiting the depth of recursion can help with this. For example, `convert h using 1` will work
in this case.

The syntax `convert ← e` will reverse the direction of the new goals
(producing `⊢ 2 * n = n + n` in this example).

Internally, `convert e` works by creating a new goal asserting that
the goal equals the type of `e`, then simplifying it using
`congr!`. The syntax `convert e using n` can be used to control the
depth of matching (like `congr! n`). In the example, `convert e using 1`
would produce a new goal `⊢ n + n + 1 = 2 * n + 1`.

Refer to the `congr!` tactic to understand the congruence operations. One of its many
features is that if `x y : t` and an instance `Subsingleton t` is in scope,
then any goals of the form `x = y` are solved automatically.

Like `congr!`, `convert` takes an optional `with` clause of `rintro` patterns,
for example `convert e using n with x y z`.

The `convert` tactic also takes a configuration option, for example
```lean
convert (config := {transparency := .default}) h
```
These are passed to `congr!`. See `Congr!.Config` for options.

# convert_to
Defined in: `Mathlib.Tactic.convertTo`

`convert_to g using n` attempts to change the current goal to `g`, but unlike `change`,
it will generate equality proof obligations using `congr! n` to resolve discrepancies.
`convert_to g` defaults to using `congr! 1`.
`convert_to` is similar to `convert`, but `convert_to` takes a type (the desired subgoal) while
`convert` takes a proof term.
That is, `convert_to g using n` is equivalent to `convert (?_ : g) using n`.

The syntax for `convert_to` is the same as for `convert`, and it has variations such as
`convert_to ← g` and `convert_to (config := {transparency := .default}) g`.

# dbg_trace
Defined in: `Lean.Parser.Tactic.dbgTrace`

`dbg_trace "foo"` prints `foo` when elaborated.
Useful for debugging tactic control flow:
```
example : False ∨ True := by
  first
  | apply Or.inl; trivial; dbg_trace "left"
  | apply Or.inr; trivial; dbg_trace "right"
```

# decreasing_tactic
Defined in: `tacticDecreasing_tactic`

`decreasing_tactic` is called by default on well-founded recursions in order
to synthesize a proof that recursive calls decrease along the selected
well founded relation. It can be locally overridden by using `decreasing_by tac`
on the recursive definition, and it can also be globally extended by adding
more definitions for `decreasing_tactic` (or `decreasing_trivial`,
which this tactic calls).

# decreasing_trivial
Defined in: `tacticDecreasing_trivial`

Extensible helper tactic for `decreasing_tactic`. This handles the "base case"
reasoning after applying lexicographic order lemmas.
It can be extended by adding more macro definitions, e.g.
```
macro_rules | `(tactic| decreasing_trivial) => `(tactic| linarith)
```

# decreasing_with
Defined in: `tacticDecreasing_with_`

Constructs a proof of decreasing along a well founded relation, by applying
lexicographic order lemmas and using `ts` to solve the base case. If it fails,
it prints a message to help the user diagnose an ill-founded recursive definition.

# delta
Defined in: `Lean.Parser.Tactic.delta`

`delta id1 id2 ...` delta-expands the definitions `id1`, `id2`, ....
This is a low-level tactic, it will expose how recursive definitions have been
compiled by Lean.

# discrete_cases
Defined in: `CategoryTheory.Discrete.tacticDiscrete_cases`

A simple tactic to run `cases` on any `Discrete α` hypotheses.

# done
Defined in: `Lean.Parser.Tactic.done`

`done` succeeds iff there are no remaining goals.

# dsimp
Defined in: `Lean.Parser.Tactic.dsimp`

The `dsimp` tactic is the definitional simplifier. It is similar to `simp` but only
applies theorems that hold by reflexivity. Thus, the result is guaranteed to be
definitionally equal to the input.

# dsimp!
Defined in: `Lean.Parser.Tactic.dsimpAutoUnfold`

`dsimp!` is shorthand for `dsimp` with `autoUnfold := true`.
This will rewrite with all equation lemmas, which can be used to
partially evaluate many definitions.

# dsimp?
Defined in: `Std.Tactic.dsimpTrace`

`simp?` takes the same arguments as `simp`, but reports an equivalent call to `simp only`
that would be sufficient to close the goal. This is useful for reducing the size of the simp
set in a local invocation to speed up processing.
```
example (x : Nat) : (if True then x + 2 else 3) = x + 2 := by
  simp? -- prints "Try this: simp only [ite_true]"
```

This command can also be used in `simp_all` and `dsimp`.

# dsimp?!
Defined in: `Std.Tactic.tacticDsimp?!_`

`simp?` takes the same arguments as `simp`, but reports an equivalent call to `simp only`
that would be sufficient to close the goal. This is useful for reducing the size of the simp
set in a local invocation to speed up processing.
```
example (x : Nat) : (if True then x + 2 else 3) = x + 2 := by
  simp? -- prints "Try this: simp only [ite_true]"
```

This command can also be used in `simp_all` and `dsimp`.

# eapply
Defined in: `Std.Tactic.tacticEapply_`

`eapply e` is like `apply e` but it does not add subgoals for variables that appear
in the types of other goals. Note that this can lead to a failure where there are
no goals remaining but there are still metavariables in the term:
```
example (h : ∀ x : Nat, x = x → True) : True := by
  eapply h
  rfl
  -- no goals
-- (kernel) declaration has metavariables '_example'
```

# econstructor
Defined in: `tacticEconstructor`

`econstructor` is like `constructor`
(it calls `apply` using the first matching constructor of an inductive datatype)
except only non-dependent premises are added as new goals.

# elementwise
Defined in: `Tactic.Elementwise.tacticElementwise___`


# elementwise!
Defined in: `Tactic.Elementwise.tacticElementwise!___`


# eq_refl
Defined in: `Lean.Parser.Tactic.refl`

`eq_refl` is equivalent to `exact rfl`, but has a few optimizations.

# erw
Defined in: `Lean.Parser.Tactic.tacticErw__`

`erw [rules]` is a shorthand for `rw (config := { transparency := .default }) [rules]`.
This does rewriting up to unfolding of regular definitions (by comparison to regular `rw`
which only unfolds `@[reducible]` definitions).

# eta_expand
Defined in: `Mathlib.Tactic.etaExpandStx`

`eta_expand at loc` eta expands all sub-expressions at the given location.
It also beta reduces any applications of eta expanded terms, so it puts it
into an eta-expanded "normal form."
This also exists as a `conv`-mode tactic.

For example, if `f` takes two arguments, then `f` becomes `fun x y => f x y`
and `f x` becomes `fun y => f x y`.

This can be useful to turn, for example, a raw `HAdd.hAdd` into `fun x y => x + y`.

# eta_reduce
Defined in: `Mathlib.Tactic.etaReduceStx`

`eta_reduce at loc` eta reduces all sub-expressions at the given location.
This also exists as a `conv`-mode tactic.

For example, `fun x y => f x y` becomes `f` after eta reduction.

# eta_struct
Defined in: `Mathlib.Tactic.etaStructStx`

`eta_struct at loc` transforms structure constructor applications such as `S.mk x.1 ... x.n`
(pretty printed as, for example, `{a := x.a, b := x.b, ...}`) into `x`.
This also exists as a `conv`-mode tactic.

The transformation is known as eta reduction for structures, and it yields definitionally
equal expressions.

For example, given `x : α × β`, then `(x.1, x.2)` becomes `x` after this transformation.

# exact
Defined in: `Lean.Parser.Tactic.exact`

`exact e` closes the main goal if its target type matches that of `e`.

# exact!?
Defined in: `Mathlib.Tactic.LibrarySearch.exact!?`


# exact?
Defined in: `Mathlib.Tactic.LibrarySearch.exact?'`


# exact?!
Defined in: `Mathlib.Tactic.LibrarySearch.exact?!`


# exact_mod_cast
Defined in: `Tactic.NormCast.tacticExact_mod_cast_`

Normalize the goal and the given expression, then close the goal with exact.

# exacts
Defined in: `Std.Tactic.exacts`

Like `exact`, but takes a list of terms and checks that all goals are discharged after the tactic.

# exfalso
Defined in: `Std.Tactic.tacticExfalso`

`exfalso` converts a goal `⊢ tgt` into `⊢ False` by applying `False.elim`.

# exists
Defined in: `Lean.Parser.Tactic.«tacticExists_,,»`

`exists e₁, e₂, ...` is shorthand for `refine ⟨e₁, e₂, ...⟩; try trivial`.
It is useful for existential goals.

# existsi
Defined in: `Mathlib.Tactic.«tacticExistsi_,,»`

`existsi e₁, e₂, ⋯` applies the tactic `refine ⟨e₁, e₂, ⋯, ?_⟩`. It's purpose is to instantiate
existential quantifiers.

Examples:

```lean
example : ∃ x : Nat, x = x := by
  existsi 42
  rfl

example : ∃ x : Nat, ∃ y : Nat, x = y := by
  existsi 42, 42
  rfl
```

# ext
Defined in: `Std.Tactic.Ext.«tacticExt___:_»`

* `ext pat*`: Apply extensionality lemmas as much as possible,
  using `pat*` to introduce the variables in extensionality lemmas like `funext`.
* `ext`: introduce anonymous variables whenever needed.
* `ext pat* : n`: apply ext lemmas only up to depth `n`.

# ext1
Defined in: `Std.Tactic.Ext.tacticExt1___`

`ext1 pat*` is like `ext pat*` except it only applies one extensionality lemma instead
of recursing as much as possible.

# ext1?
Defined in: `Std.Tactic.Ext.tacticExt1?___`

`ext1? pat*` is like `ext1 pat*` but gives a suggestion on what pattern to use

# ext?
Defined in: `Std.Tactic.Ext.«tacticExt?___:_»`

`ext? pat*` is like `ext pat*` but gives a suggestion on what pattern to use

# extract_goal
Defined in: `Mathlib.Tactic.extractGoal`

`extract_goal` formats the current goal as a stand-alone theorem or definition,
and `extract_goal name` uses the name `name` instead of an autogenerated one.

It tries to produce an output that can be copy-pasted and just work,
but its success depends on whether the expressions are amenable
to being unambiguously pretty printed.

By default it cleans up the local context. To use the full local context, use `extract_goal*`.

The tactic responds to pretty printing options.
For example, `set_option pp.all true in extract_goal` gives the `pp.all` form.

# extract_lets
Defined in: `Mathlib.extractLets`

The `extract_lets at h` tactic takes a local hypothesis of the form `h : let x := v; b`
and introduces a new local definition `x := v` while changing `h` to be `h : b`.  It can be thought
of as being a `cases` tactic for `let` expressions. It can also be thought of as being like
`intros at h` for `let` expressions.

For example, if `h : let x := 1; x = x`, then `extract_lets x at h` introduces `x : Nat := 1` and
changes `h` to `h : x = x`.

Just like `intros`, the `extract_lets` tactic either takes a list of names, in which case
that specifies the number of `let` bindings that must be extracted, or it takes no names, in which
case all the `let` bindings are extracted.

The tactic `extract_let at ⊢` is a weaker form of `intros` that only introduces obvious `let`s.

# fail
Defined in: `Lean.Parser.Tactic.fail`

`fail msg` is a tactic that always fails, and produces an error using the given message.

# fail_if_no_progress
Defined in: `Mathlib.Tactic.failIfNoProgress`

`fail_if_no_progress tacs` evaluates `tacs`, and fails if no progress is made on the main goal
or the local context at reducible transparency.

# fail_if_success
Defined in: `Lean.Parser.Tactic.failIfSuccess`

`fail_if_success t` fails if the tactic `t` succeeds.

# fapply
Defined in: `Std.Tactic.tacticFapply_`

`fapply e` is like `apply e` but it adds goals in the order they appear,
rather than putting the dependent goals first.

# fconstructor
Defined in: `tacticFconstructor`

`fconstructor` is like `constructor`
(it calls `apply` using the first matching constructor of an inductive datatype)
except that it does not reorder goals.

# field_simp
Defined in: `Mathlib.Tactic.FieldSimp.fieldSimp`

The goal of `field_simp` is to reduce an expression in a field to an expression of the form `n / d`
where neither `n` nor `d` contains any division symbol, just using the simplifier (with a carefully
crafted simpset named `field_simps`) to reduce the number of division symbols whenever possible by
iterating the following steps:

- write an inverse as a division
- in any product, move the division to the right
- if there are several divisions in a product, group them together at the end and write them as a
  single division
- reduce a sum to a common denominator

If the goal is an equality, this simpset will also clear the denominators, so that the proof
can normally be concluded by an application of `ring` or `ring_exp`.

`field_simp [hx, hy]` is a short form for
`simp (discharger := Tactic.FieldSimp.discharge) [-one_div, -mul_eq_zero, hx, hy, field_simps]`

Note that this naive algorithm will not try to detect common factors in denominators to reduce the
complexity of the resulting expression. Instead, it relies on the ability of `ring` to handle
complicated expressions in the next step.

As always with the simplifier, reduction steps will only be applied if the preconditions of the
lemmas can be checked. This means that proofs that denominators are nonzero should be included. The
fact that a product is nonzero when all factors are, and that a power of a nonzero number is
nonzero, are included in the simpset, but more complicated assertions (especially dealing with sums)
should be given explicitly. If your expression is not completely reduced by the simplifier
invocation, check the denominators of the resulting expression and provide proofs that they are
nonzero to enable further progress.

To check that denominators are nonzero, `field_simp` will look for facts in the context, and
will try to apply `norm_num` to close numerical goals.

The invocation of `field_simp` removes the lemma `one_div` from the simpset, as this lemma
works against the algorithm explained above. It also removes
`mul_eq_zero : x * y = 0 ↔ x = 0 ∨ y = 0`, as `norm_num` can not work on disjunctions to
close goals of the form `24 ≠ 0`, and replaces it with `mul_ne_zero : x ≠ 0 → y ≠ 0 → x * y ≠ 0`
creating two goals instead of a disjunction.

For example,
```lean
example (a b c d x y : ℂ) (hx : x ≠ 0) (hy : y ≠ 0) :
    a + b / x + c / x^2 + d / x^3 = a + x⁻¹ * (y * b / y + (d / x + c) / x) := by
  field_simp
  ring
```

Moreover, the `field_simp` tactic can also take care of inverses of units in
a general (commutative) monoid/ring and partial division `/ₚ`, see `Algebra.Group.Units`
for the definition. Analogue to the case above, the lemma `one_divp` is removed from the simpset
as this works against the algorithm. If you have objects with an `IsUnit x` instance like
`(x : R) (hx : IsUnit x)`, you should lift them with
`lift x to Rˣ using id hx, rw [IsUnit.unit_of_val_units] clear hx`
before using `field_simp`.

See also the `cancel_denoms` tactic, which tries to do a similar simplification for expressions
that have numerals in denominators.
The tactics are not related: `cancel_denoms` will only handle numeric denominators, and will try to
entirely remove (numeric) division from the expression by multiplying by a factor.

# filter_upwards
Defined in: `Mathlib.Tactic.filterUpwards`

`filter_upwards [h₁, ⋯, hₙ]` replaces a goal of the form `s ∈ f` and terms
`h₁ : t₁ ∈ f, ⋯, hₙ : tₙ ∈ f` with `∀ x, x ∈ t₁ → ⋯ → x ∈ tₙ → x ∈ s`.
The list is an optional parameter, `[]` being its default value.

`filter_upwards [h₁, ⋯, hₙ] with a₁ a₂ ⋯ aₖ` is a short form for
`{ filter_upwards [h₁, ⋯, hₙ], intros a₁ a₂ ⋯ aₖ }`.

`filter_upwards [h₁, ⋯, hₙ] using e` is a short form for
`{ filter_upwards [h1, ⋯, hn], exact e }`.

Combining both shortcuts is done by writing `filter_upwards [h₁, ⋯, hₙ] with a₁ a₂ ⋯ aₖ using e`.
Note that in this case, the `aᵢ` terms can be used in `e`.

# fin_cases
Defined in: `Lean.Elab.Tactic.finCases`

`fin_cases h` performs case analysis on a hypothesis of the form
`h : A`, where `[Fintype A]` is available, or
`h : a ∈ A`, where `A : Finset X`, `A : Multiset X` or `A : List X`.

As an example, in
```
example (f : ℕ → Prop) (p : Fin 3) (h0 : f 0) (h1 : f 1) (h2 : f 2) : f p.val := by
  fin_cases p; simp
  all_goals assumption
```
after `fin_cases p; simp`, there are three goals, `f 0`, `f 1`, and `f 2`.

# find
Defined in: `Mathlib.Tactic.Find.tacticFind`


# first
Defined in: `Lean.Parser.Tactic.first`

`first | tac | ...` runs each `tac` until one succeeds, or else fails.

# focus
Defined in: `Lean.Parser.Tactic.focus`

`focus tac` focuses on the main goal, suppressing all other goals, and runs `tac` on it.
Usually `· tac`, which enforces that the goal is closed by `tac`, should be preferred.

# frac_tac
Defined in: `RatFunc.tacticFrac_tac`

Solve equations for `RatFunc K` by working in `FractionRing K[X]`.

# funext
Defined in: `tacticFunext___`

Apply function extensionality and introduce new hypotheses.
The tactic `funext` will keep applying the `funext` lemma until the goal target is not reducible to
```
  |-  ((fun x => ...) = (fun x => ...))
```
The variant `funext h₁ ... hₙ` applies `funext` `n` times, and uses the given identifiers to name the new hypotheses.
Patterns can be used like in the `intro` tactic. Example, given a goal
```
  |-  ((fun x : Nat × Bool => ...) = (fun x => ...))
```
`funext (a, b)` applies `funext` once and performs pattern matching on the newly introduced pair.

# gcongr
Defined in: `Mathlib.Tactic.GCongr.tacticGcongr__With__`

The `gcongr` tactic applies "generalized congruence" rules, reducing a relational goal
between a LHS and RHS matching the same pattern to relational subgoals between the differing
inputs to the pattern.  For example,
```
example {a b x c d : ℝ} (h1 : a + 1 ≤ b + 1) (h2 : c + 2 ≤ d + 2) :
    x ^ 2 * a + c ≤ x ^ 2 * b + d := by
  gcongr
  · linarith
  · linarith
```
This example has the goal of proving the relation `≤` between a LHS and RHS both of the pattern
```
x ^ 2 * ?_ + ?_
```
(with inputs `a`, `c` on the left and `b`, `d` on the right); after the use of
`gcongr`, we have the simpler goals `a ≤ b` and `c ≤ d`.

A pattern can be provided explicitly; this is useful if a non-maximal match is desired:
```
example {a b c d x : ℝ} (h : a + c + 1 ≤ b + d + 1) :
    x ^ 2 * (a + c) + 5 ≤ x ^ 2 * (b + d) + 5 := by
  gcongr x ^ 2 * ?_ + 5
  linarith
```

The "generalized congruence" rules used are the library lemmas which have been tagged with the
attribute `@[gcongr]`.  For example, the first example constructs the proof term
```
add_le_add (mul_le_mul_of_nonneg_left _ (pow_bit0_nonneg x 1)) _
```
using the generalized congruence lemmas `add_le_add` and `mul_le_mul_of_nonneg_left`.

The tactic attempts to discharge side goals to these "generalized congruence" lemmas (such as the
side goal `0 ≤ x ^ 2` in the above application of `mul_le_mul_of_nonneg_left`) using the tactic
`gcongr_discharger`, which wraps `positivity` but can also be extended. Side goals not discharged
in this way are left for the user.

# gcongr_discharger
Defined in: `Mathlib.Tactic.GCongr.tacticGcongr_discharger`


# generalize
Defined in: `Lean.Parser.Tactic.generalize`

* `generalize ([h :] e = x),+` replaces all occurrences `e`s in the main goal
  with a fresh hypothesis `x`s. If `h` is given, `h : e = x` is introduced as well.
* `generalize e = x at h₁ ... hₙ` also generalizes occurrences of `e`
  inside `h₁`, ..., `hₙ`.
* `generalize e = x at *` will generalize occurrences of `e` everywhere.

# generalize_proofs
Defined in: `Mathlib.Tactic.GeneralizeProofs.generalizeProofs`

Generalize proofs in the goal, naming them with the provided list.

For example:
```lean
example : List.nthLe [1, 2] 1 dec_trivial = 2 := by
  -- ⊢ [1, 2].nthLe 1 _ = 2
  generalize_proofs h,
  -- h : 1 < [1, 2].length
  -- ⊢ [1, 2].nthLe 1 h = 2
```

# get_elem_tactic
Defined in: `tacticGet_elem_tactic`

`get_elem_tactic` is the tactic automatically called by the notation `arr[i]`
to prove any side conditions that arise when constructing the term
(e.g. the index is in bounds of the array). It just delegates to
`get_elem_tactic_trivial` and gives a diagnostic error message otherwise;
users are encouraged to extend `get_elem_tactic_trivial` instead of this tactic.

# get_elem_tactic_trivial
Defined in: `tacticGet_elem_tactic_trivial`

`get_elem_tactic_trivial` is an extensible tactic automatically called
by the notation `arr[i]` to prove any side conditions that arise when
constructing the term (e.g. the index is in bounds of the array).
The default behavior is to just try `trivial` (which handles the case
where `i < arr.size` is in the context) and `simp_arith`
(for doing linear arithmetic in the index).

# group
Defined in: `Mathlib.Tactic.Group.group`

Tactic for normalizing expressions in multiplicative groups, without assuming
commutativity, using only the group axioms without any information about which group
is manipulated.

(For additive commutative groups, use the `abel` tactic instead.)

Example:
```lean
example {G : Type} [Group G] (a b c d : G) (h : c = (a*b^2)*((b*b)⁻¹*a⁻¹)*d) : a*c*d⁻¹ = a :=
begin
  group at h, -- normalizes `h` which becomes `h : c = d`
  rw h,       -- the goal is now `a*d*d⁻¹ = a`
  group,      -- which then normalized and closed
end
```

# guard_expr
Defined in: `Std.Tactic.GuardExpr.guardExpr`

Tactic to check equality of two expressions.
* `guard_expr e = e'` checks that `e` and `e'` are defeq at reducible transparency.
* `guard_expr e =~ e'` checks that `e` and `e'` are defeq at default transparency.
* `guard_expr e =ₛ e'` checks that `e` and `e'` are syntactically equal.
* `guard_expr e =ₐ e'` checks that `e` and `e'` are alpha-equivalent.

Both `e` and `e'` are elaborated then have their metavariables instantiated before the equality
check. Their types are unified (using `isDefEqGuarded`) before synthetic metavariables are
processed, which helps with default instance handling.

# guard_goal_nums
Defined in: `guardGoalNums`

`guard_goal_nums n` succeeds if there are exactly `n` goals and fails otherwise.

# guard_hyp
Defined in: `Std.Tactic.GuardExpr.guardHyp`

Tactic to check that a named hypothesis has a given type and/or value.

* `guard_hyp h : t` checks the type up to reducible defeq,
* `guard_hyp h :~ t` checks the type up to default defeq,
* `guard_hyp h :ₛ t` checks the type up to syntactic equality,
* `guard_hyp h :ₐ t` checks the type up to alpha equality.
* `guard_hyp h := v` checks value up to reducible defeq,
* `guard_hyp h :=~ v` checks value up to default defeq,
* `guard_hyp h :=ₛ v` checks value up to syntactic equality,
* `guard_hyp h :=ₐ v` checks the value up to alpha equality.

The value `v` is elaborated using the type of `h` as the expected type.

# guard_hyp_nums
Defined in: `guardHypNums`

`guard_hyp_nums n` succeeds if there are exactly `n` hypotheses and fails otherwise.

Note that, depending on what options are set, some hypotheses in the local context might
not be printed in the goal view. This tactic computes the total number of hypotheses,
not the number of visible hypotheses.

# guard_target
Defined in: `Std.Tactic.GuardExpr.guardTarget`

Tactic to check that the target agrees with a given expression.
* `guard_target = e` checks that the target is defeq at reducible transparency to `e`.
* `guard_target =~ e` checks that the target is defeq at default transparency to `e`.
* `guard_target =ₛ e` checks that the target is syntactically equal to `e`.
* `guard_target =ₐ e` checks that the target is alpha-equivalent to `e`.

The term `e` is elaborated with the type of the goal as the expected type, which is mostly
useful within `conv` mode.

# have
Defined in: `Lean.Parser.Tactic.tacticHave_`

`have h : t := e` adds the hypothesis `h : t` to the current goal if `e` a term
of type `t`.
* If `t` is omitted, it will be inferred.
* If `h` is omitted, the name `this` is used.
* The variant `have pattern := e` is equivalent to `match e with | pattern => _`,
  and it is convenient for types that have only one applicable constructor.
  For example, given `h : p ∧ q ∧ r`, `have ⟨h₁, h₂, h₃⟩ := h` produces the
  hypotheses `h₁ : p`, `h₂ : q`, and `h₃ : r`.

# have
Defined in: `Mathlib.Tactic.tacticHave_`


# have!?
Defined in: `Mathlib.Tactic.Propose.«tacticHave!?:_Using__»`

* `have? using a, b, c` tries to find a lemma
which makes use of each of the local hypotheses `a, b, c`,
and reports any results via trace messages.
* `have? : h using a, b, c` only returns lemmas whose type matches `h` (which may contain `_`).
* `have?! using a, b, c` will also call `have` to add results to the local goal state.

Note that `have?` (unlike `apply?`) does not inspect the goal at all,
only the types of the lemmas in the `using` clause.

`have?` should not be left in proofs; it is a search tool, like `apply?`.

Suggestions are printed as `have := f a b c`.

# have'
Defined in: `Lean.Parser.Tactic.tacticHave'_`

Similar to `have`, but using `refine'`

# have'
Defined in: `Lean.Parser.Tactic.«tacticHave'_:=_»`

Similar to `have`, but using `refine'`

# have?
Defined in: `Mathlib.Tactic.Propose.propose'`

* `have? using a, b, c` tries to find a lemma
which makes use of each of the local hypotheses `a, b, c`,
and reports any results via trace messages.
* `have? : h using a, b, c` only returns lemmas whose type matches `h` (which may contain `_`).
* `have?! using a, b, c` will also call `have` to add results to the local goal state.

Note that `have?` (unlike `apply?`) does not inspect the goal at all,
only the types of the lemmas in the `using` clause.

`have?` should not be left in proofs; it is a search tool, like `apply?`.

Suggestions are printed as `have := f a b c`.

# have?!
Defined in: `Mathlib.Tactic.Propose.«tacticHave?!:_Using__»`

* `have? using a, b, c` tries to find a lemma
which makes use of each of the local hypotheses `a, b, c`,
and reports any results via trace messages.
* `have? : h using a, b, c` only returns lemmas whose type matches `h` (which may contain `_`).
* `have?! using a, b, c` will also call `have` to add results to the local goal state.

Note that `have?` (unlike `apply?`) does not inspect the goal at all,
only the types of the lemmas in the `using` clause.

`have?` should not be left in proofs; it is a search tool, like `apply?`.

Suggestions are printed as `have := f a b c`.

# haveI
Defined in: `Std.Tactic.tacticHaveI_`

`haveI` behaves like `have`, but inlines the value instead of producing a `let_fun` term.

# induction
Defined in: `Lean.Parser.Tactic.induction`

Assuming `x` is a variable in the local context with an inductive type,
`induction x` applies induction on `x` to the main goal,
producing one goal for each constructor of the inductive type,
in which the target is replaced by a general instance of that constructor
and an inductive hypothesis is added for each recursive argument to the constructor.
If the type of an element in the local context depends on `x`,
that element is reverted and reintroduced afterward,
so that the inductive hypothesis incorporates that hypothesis as well.

For example, given `n : Nat` and a goal with a hypothesis `h : P n` and target `Q n`,
`induction n` produces one goal with hypothesis `h : P 0` and target `Q 0`,
and one goal with hypotheses `h : P (Nat.succ a)` and `ih₁ : P a → Q a` and target `Q (Nat.succ a)`.
Here the names `a` and `ih₁` are chosen automatically and are not accessible.
You can use `with` to provide the variables names for each constructor.
- `induction e`, where `e` is an expression instead of a variable,
  generalizes `e` in the goal, and then performs induction on the resulting variable.
- `induction e using r` allows the user to specify the principle of induction that should be used.
  Here `r` should be a theorem whose result type must be of the form `C t`,
  where `C` is a bound variable and `t` is a (possibly empty) sequence of bound variables
- `induction e generalizing z₁ ... zₙ`, where `z₁ ... zₙ` are variables in the local context,
  generalizes over `z₁ ... zₙ` before applying the induction but then introduces them in each goal.
  In other words, the net effect is that each inductive hypothesis is generalized.
- Given `x : Nat`, `induction x with | zero => tac₁ | succ x' ih => tac₂`
  uses tactic `tac₁` for the `zero` case, and `tac₂` for the `succ` case.

# induction'
Defined in: `Mathlib.Tactic.induction'`


# infer_instance
Defined in: `Lean.Parser.Tactic.tacticInfer_instance`

`infer_instance` is an abbreviation for `exact inferInstance`.
It synthesizes a value of any target type by typeclass inference.

# infer_param
Defined in: `Mathlib.Tactic.inferOptParam`

Close a goal of the form `optParam α a` or `autoParam α stx` by using `a`.

# inhabit
Defined in: `Lean.Elab.Tactic.inhabit`

`inhabit α` tries to derive a `Nonempty α` instance and
then uses it to make an `Inhabited α` instance.
If the target is a `Prop`, this is done constructively. Otherwise, it uses `Classical.choice`.

# injection
Defined in: `Lean.Parser.Tactic.injection`

The `injection` tactic is based on the fact that constructors of inductive data
types are injections.
That means that if `c` is a constructor of an inductive datatype, and if `(c t₁)`
and `(c t₂)` are two terms that are equal then  `t₁` and `t₂` are equal too.
If `q` is a proof of a statement of conclusion `t₁ = t₂`, then injection applies
injectivity to derive the equality of all arguments of `t₁` and `t₂` placed in
the same positions. For example, from `(a::b) = (c::d)` we derive `a=c` and `b=d`.
To use this tactic `t₁` and `t₂` should be constructor applications of the same constructor.
Given `h : a::b = c::d`, the tactic `injection h` adds two new hypothesis with types
`a = c` and `b = d` to the main goal.
The tactic `injection h with h₁ h₂` uses the names `h₁` and `h₂` to name the new hypotheses.

# injections
Defined in: `Lean.Parser.Tactic.injections`

`injections` applies `injection` to all hypotheses recursively
(since `injection` can produce new hypotheses). Useful for destructing nested
constructor equalities like `(a::b::c) = (d::e::f)`.

# interval_cases
Defined in: `Mathlib.Tactic.intervalCases`

`interval_cases n` searches for upper and lower bounds on a variable `n`,
and if bounds are found,
splits into separate cases for each possible value of `n`.

As an example, in
```
example (n : ℕ) (w₁ : n ≥ 3) (w₂ : n < 5) : n = 3 ∨ n = 4 := by
  interval_cases n
  all_goals simp
```
after `interval_cases n`, the goals are `3 = 3 ∨ 3 = 4` and `4 = 3 ∨ 4 = 4`.

You can also explicitly specify a lower and upper bound to use,
as `interval_cases using hl, hu`.
The hypotheses should be in the form `hl : a ≤ n` and `hu : n < b`,
in which case `interval_cases` calls `fin_cases` on the resulting fact `n ∈ Set.Ico a b`.

You can specify a name `h` for the new hypothesis,
as `interval_cases h : n` or `interval_cases h : n using hl, hu`.

# intro
Defined in: `Lean.Parser.Tactic.intro`

Introduces one or more hypotheses, optionally naming and/or pattern-matching them.
For each hypothesis to be introduced, the remaining main goal's target type must
be a `let` or function type.

* `intro` by itself introduces one anonymous hypothesis, which can be accessed
  by e.g. `assumption`.
* `intro x y` introduces two hypotheses and names them. Individual hypotheses
  can be anonymized via `_`, or matched against a pattern:
  ```lean
  -- ... ⊢ α × β → ...
  intro (a, b)
  -- ..., a : α, b : β ⊢ ...
  ```
* Alternatively, `intro` can be combined with pattern matching much like `fun`:
  ```lean
  intro
  | n + 1, 0 => tac
  | ...
  ```

# intro
Defined in: `Std.Tactic.«tacticIntro.»`

The tactic `intro.` is shorthand for `exact fun.`: it introduces the assumptions, then performs an
empty pattern match, closing the goal if the introduced pattern is impossible.

# intros
Defined in: `Lean.Parser.Tactic.intros`

`intros x...` behaves like `intro x...`, but then keeps introducing (anonymous)
hypotheses until goal is not of a function type.

# introv
Defined in: `Mathlib.Tactic.introv`

The tactic `introv` allows the user to automatically introduce the variables of a theorem and
explicitly name the non-dependent hypotheses.
Any dependent hypotheses are assigned their default names.

Examples:
```
example : ∀ a b : Nat, a = b → b = a := by
  introv h,
  exact h.symm
```
The state after `introv h` is
```
a b : ℕ,
h : a = b
⊢ b = a
```

```
example : ∀ a b : Nat, a = b → ∀ c, b = c → a = c := by
  introv h₁ h₂,
  exact h₁.trans h₂
```
The state after `introv h₁ h₂` is
```
a b : ℕ,
h₁ : a = b,
c : ℕ,
h₂ : b = c
⊢ a = c
```

# isBoundedDefault
Defined in: `Filter.tacticIsBoundedDefault`

Filters are automatically bounded or cobounded in complete lattices. To use the same statements
in complete and conditionally complete lattices but let automation fill automatically the
boundedness proofs in complete lattices, we use the tactic `isBoundedDefault` in the statements,
in the form `(hf : f.IsBounded (≥) := by isBoundedDefault)`.

# iterate
Defined in: `Std.Tactic.tacticIterate____`

`iterate n tac` runs `tac` exactly `n` times.
`iterate tac` runs `tac` repeatedly until failure.

To run multiple tactics, one can do `iterate (tac₁; tac₂; ⋯)` or
```lean
iterate
  tac₁
  tac₂
  ⋯
```

# left
Defined in: `Mathlib.Tactic.tacticLeft`


# let
Defined in: `Lean.Parser.Tactic.letrec`

`let rec f : t := e` adds a recursive definition `f` to the current goal.
The syntax is the same as term-mode `let rec`.

# let
Defined in: `Mathlib.Tactic.tacticLet_`


# let
Defined in: `Lean.Parser.Tactic.tacticLet_`

`let h : t := e` adds the hypothesis `h : t := e` to the current goal if `e` a term of type `t`.
If `t` is omitted, it will be inferred.
The variant `let pattern := e` is equivalent to `match e with | pattern => _`,
and it is convenient for types that have only applicable constructor.
Example: given `h : p ∧ q ∧ r`, `let ⟨h₁, h₂, h₃⟩ := h` produces the hypotheses
`h₁ : p`, `h₂ : q`, and `h₃ : r`.

# let'
Defined in: `Lean.Parser.Tactic.tacticLet'_`

Similar to `let`, but using `refine'`

# letI
Defined in: `Std.Tactic.tacticLetI_`

`letI` behaves like `let`, but inlines the value instead of producing a `let_fun` term.

# library_search
Defined in: `Mathlib.Tactic.LibrarySearch.tacticLibrary_search`


# lift
Defined in: `Mathlib.Tactic.lift`

Lift an expression to another type.
* Usage: `'lift' expr 'to' expr ('using' expr)? ('with' id (id id?)?)?`.
* If `n : ℤ` and `hn : n ≥ 0` then the tactic `lift n to ℕ using hn` creates a new
  constant of type `ℕ`, also named `n` and replaces all occurrences of the old variable `(n : ℤ)`
  with `↑n` (where `n` in the new variable). It will remove `n` and `hn` from the context.
  + So for example the tactic `lift n to ℕ using hn` transforms the goal
    `n : ℤ, hn : n ≥ 0, h : P n ⊢ n = 3` to `n : ℕ, h : P ↑n ⊢ ↑n = 3`
    (here `P` is some term of type `ℤ → Prop`).
* The argument `using hn` is optional, the tactic `lift n to ℕ` does the same, but also creates a
  new subgoal that `n ≥ 0` (where `n` is the old variable).
  This subgoal will be placed at the top of the goal list.
  + So for example the tactic `lift n to ℕ` transforms the goal
    `n : ℤ, h : P n ⊢ n = 3` to two goals
    `n : ℤ, h : P n ⊢ n ≥ 0` and `n : ℕ, h : P ↑n ⊢ ↑n = 3`.
* You can also use `lift n to ℕ using e` where `e` is any expression of type `n ≥ 0`.
* Use `lift n to ℕ with k` to specify the name of the new variable.
* Use `lift n to ℕ with k hk` to also specify the name of the equality `↑k = n`. In this case, `n`
  will remain in the context. You can use `rfl` for the name of `hk` to substitute `n` away
  (i.e. the default behavior).
* You can also use `lift e to ℕ with k hk` where `e` is any expression of type `ℤ`.
  In this case, the `hk` will always stay in the context, but it will be used to rewrite `e` in
  all hypotheses and the target.
  + So for example the tactic `lift n + 3 to ℕ using hn with k hk` transforms the goal
    `n : ℤ, hn : n + 3 ≥ 0, h : P (n + 3) ⊢ n + 3 = 2 * n` to the goal
    `n : ℤ, k : ℕ, hk : ↑k = n + 3, h : P ↑k ⊢ ↑k = 2 * n`.
* The tactic `lift n to ℕ using h` will remove `h` from the context. If you want to keep it,
  specify it again as the third argument to `with`, like this: `lift n to ℕ using h with n rfl h`.
* More generally, this can lift an expression from `α` to `β` assuming that there is an instance
  of `CanLift α β`. In this case the proof obligation is specified by `CanLift.prf`.
* Given an instance `CanLift β γ`, it can also lift `α → β` to `α → γ`; more generally, given
  `β : Π a : α, Type*`, `γ : Π a : α, Type*`, and `[Π a : α, CanLift (β a) (γ a)]`, it
  automatically generates an instance `CanLift (Π a, β a) (Π a, γ a)`.

`lift` is in some sense dual to the `zify` tactic. `lift (z : ℤ) to ℕ` will change the type of an
integer `z` (in the supertype) to `ℕ` (the subtype), given a proof that `z ≥ 0`;
propositions concerning `z` will still be over `ℤ`. `zify` changes propositions about `ℕ` (the
subtype) to propositions about `ℤ` (the supertype), without changing the type of any variable.

# lift_lets
Defined in: `Mathlib.Tactic.lift_lets`

Lift all the `let` bindings in the type of an expression as far out as possible.

When applied to the main goal, this gives one the ability to `intro` embedded `let` expressions.
For example,
```lean
example : (let x := 1; x) = 1 := by
  lift_lets
  -- ⊢ let x := 1; x = 1
  intro x
  sorry
```

During the lifting process, let bindings are merged if they have the same type and value.

# liftable_prefixes
Defined in: `Mathlib.Tactic.Coherence.liftable_prefixes`

Internal tactic used in `coherence`.

Rewrites an equation `f = g` as `f₀ ≫ f₁ = g₀ ≫ g₁`,
where `f₀` and `g₀` are maximal prefixes of `f` and `g` (possibly after reassociating)
which are "liftable" (i.e. expressible as compositions of unitors and associators).

# linarith
Defined in: `linarith`

`linarith` attempts to find a contradiction between hypotheses that are linear (in)equalities.
Equivalently, it can prove a linear inequality by assuming its negation and proving `False`.

In theory, `linarith` should prove any goal that is true in the theory of linear arithmetic over
the rationals. While there is some special handling for non-dense orders like `Nat` and `Int`,
this tactic is not complete for these theories and will not prove every true goal. It will solve
goals over arbitrary types that instantiate `LinearOrderedCommRing`.

An example:
```lean
example (x y z : ℚ) (h1 : 2*x < 3*y) (h2 : -4*x + 2*z < 0)
        (h3 : 12*y - 4* z < 0)  : False :=
by linarith
```

`linarith` will use all appropriate hypotheses and the negation of the goal, if applicable.

`linarith [t1, t2, t3]` will additionally use proof terms `t1, t2, t3`.

`linarith only [h1, h2, h3, t1, t2, t3]` will use only the goal (if relevant), local hypotheses
`h1`, `h2`, `h3`, and proofs `t1`, `t2`, `t3`. It will ignore the rest of the local context.

`linarith!` will use a stronger reducibility setting to try to identify atoms. For example,
```lean
example (x : ℚ) : id x ≥ x :=
by linarith
```
will fail, because `linarith` will not identify `x` and `id x`. `linarith!` will.
This can sometimes be expensive.

`linarith (config := { .. })` takes a config object with five
optional arguments:
* `discharger` specifies a tactic to be used for reducing an algebraic equation in the
  proof stage. The default is `ring`. Other options include `simp` for basic
  problems.
* `transparency` controls how hard `linarith` will try to match atoms to each other. By default
  it will only unfold `reducible` definitions.
* If `split_hypotheses` is true, `linarith` will split conjunctions in the context into separate
  hypotheses.
* If `exfalso` is false, `linarith` will fail when the goal is neither an inequality nor `false`.
  (True by default.)
* `restrict_type` (not yet implemented in mathlib4)
  will only use hypotheses that are inequalities over `tp`. This is useful
  if you have e.g. both integer and rational valued inequalities in the local context, which can
  sometimes confuse the tactic.

A variant, `nlinarith`, does some basic preprocessing to handle some nonlinear goals.

The option `set_option trace.linarith true` will trace certain intermediate stages of the `linarith`
routine.

# linarith!
Defined in: `tacticLinarith!_`

`linarith` attempts to find a contradiction between hypotheses that are linear (in)equalities.
Equivalently, it can prove a linear inequality by assuming its negation and proving `False`.

In theory, `linarith` should prove any goal that is true in the theory of linear arithmetic over
the rationals. While there is some special handling for non-dense orders like `Nat` and `Int`,
this tactic is not complete for these theories and will not prove every true goal. It will solve
goals over arbitrary types that instantiate `LinearOrderedCommRing`.

An example:
```lean
example (x y z : ℚ) (h1 : 2*x < 3*y) (h2 : -4*x + 2*z < 0)
        (h3 : 12*y - 4* z < 0)  : False :=
by linarith
```

`linarith` will use all appropriate hypotheses and the negation of the goal, if applicable.

`linarith [t1, t2, t3]` will additionally use proof terms `t1, t2, t3`.

`linarith only [h1, h2, h3, t1, t2, t3]` will use only the goal (if relevant), local hypotheses
`h1`, `h2`, `h3`, and proofs `t1`, `t2`, `t3`. It will ignore the rest of the local context.

`linarith!` will use a stronger reducibility setting to try to identify atoms. For example,
```lean
example (x : ℚ) : id x ≥ x :=
by linarith
```
will fail, because `linarith` will not identify `x` and `id x`. `linarith!` will.
This can sometimes be expensive.

`linarith (config := { .. })` takes a config object with five
optional arguments:
* `discharger` specifies a tactic to be used for reducing an algebraic equation in the
  proof stage. The default is `ring`. Other options include `simp` for basic
  problems.
* `transparency` controls how hard `linarith` will try to match atoms to each other. By default
  it will only unfold `reducible` definitions.
* If `split_hypotheses` is true, `linarith` will split conjunctions in the context into separate
  hypotheses.
* If `exfalso` is false, `linarith` will fail when the goal is neither an inequality nor `false`.
  (True by default.)
* `restrict_type` (not yet implemented in mathlib4)
  will only use hypotheses that are inequalities over `tp`. This is useful
  if you have e.g. both integer and rational valued inequalities in the local context, which can
  sometimes confuse the tactic.

A variant, `nlinarith`, does some basic preprocessing to handle some nonlinear goals.

The option `set_option trace.linarith true` will trace certain intermediate stages of the `linarith`
routine.

# linear_combination
Defined in: `Mathlib.Tactic.LinearCombination.linearCombination`

`linear_combination` attempts to simplify the target by creating a linear combination
  of a list of equalities and subtracting it from the target.
  The tactic will create a linear
  combination by adding the equalities together from left to right, so the order
  of the input hypotheses does matter.  If the `normalize` field of the
  configuration is set to false, then the tactic will simply set the user up to
  prove their target using the linear combination instead of normalizing the subtraction.

Note: The left and right sides of all the equalities should have the same
  type, and the coefficients should also have this type.  There must be
  instances of `Mul` and `AddGroup` for this type.

* The input `e` in `linear_combination e` is a linear combination of proofs of equalities,
  given as a sum/difference of coefficients multiplied by expressions.
  The coefficients may be arbitrary expressions.
  The expressions can be arbitrary proof terms proving equalities.
  Most commonly they are hypothesis names `h1, h2, ...`.
* `linear_combination (norm := tac) e` runs the "normalization tactic" `tac`
  on the subgoal(s) after constructing the linear combination.
  * The default normalization tactic is `ring1`, which closes the goal or fails.
  * To get a subgoal in the case that it is not immediately provable, use
    `ring_nf` as the normalization tactic.
  * To avoid normalization entirely, use `skip` as the normalization tactic.
* `linear_combination2 e` is the same as `linear_combination e` but it produces two
  subgoals instead of one: rather than proving that `(a - b) - (a' - b') = 0` where
  `a' = b'` is the linear combination from `e` and `a = b` is the goal,
  it instead attempts to prove `a = a'` and `b = b'`.
  Because it does not use subtraction, this form is applicable also to semirings.
  * Note that a goal which is provable by `linear_combination e` may not be provable
    by `linear_combination2 e`; in general you may need to add a coefficient to `e`
    to make both sides match, as in `linear_combination2 e + c`.
  * You can also reverse equalities using `← h`, so for example if `h₁ : a = b`
    then `2 * (← h)` is a proof of `2 * b = 2 * a`.

Example Usage:
```
example (x y : ℤ) (h1 : x*y + 2*x = 1) (h2 : x = y) : x*y = -2*y + 1 := by
  linear_combination 1*h1 - 2*h2

example (x y : ℤ) (h1 : x*y + 2*x = 1) (h2 : x = y) : x*y = -2*y + 1 := by
  linear_combination h1 - 2*h2

example (x y : ℤ) (h1 : x*y + 2*x = 1) (h2 : x = y) : x*y = -2*y + 1 := by
  linear_combination (norm := ring_nf) -2*h2
  /- Goal: x * y + x * 2 - 1 = 0 -/

example (x y z : ℝ) (ha : x + 2*y - z = 4) (hb : 2*x + y + z = -2)
    (hc : x + 2*y + z = 2) :
    -3*x - 3*y - 4*z = 2 := by
  linear_combination ha - hb - 2*hc

example (x y : ℚ) (h1 : x + y = 3) (h2 : 3*x = 7) :
    x*x*y + y*x*y + 6*x = 3*x*y + 14 := by
  linear_combination x*y*h1 + 2*h2

example (x y : ℤ) (h1 : x = -3) (h2 : y = 10) : 2*x = -6 := by
  linear_combination (norm := skip) 2*h1
  simp

axiom qc : ℚ
axiom hqc : qc = 2*qc

example (a b : ℚ) (h : ∀ p q : ℚ, p = q) : 3*a + qc = 3*b + 2*qc := by
  linear_combination 3 * h a b + hqc
```

# linear_combination2
Defined in: `Mathlib.Tactic.LinearCombination.tacticLinear_combination2____`

`linear_combination` attempts to simplify the target by creating a linear combination
  of a list of equalities and subtracting it from the target.
  The tactic will create a linear
  combination by adding the equalities together from left to right, so the order
  of the input hypotheses does matter.  If the `normalize` field of the
  configuration is set to false, then the tactic will simply set the user up to
  prove their target using the linear combination instead of normalizing the subtraction.

Note: The left and right sides of all the equalities should have the same
  type, and the coefficients should also have this type.  There must be
  instances of `Mul` and `AddGroup` for this type.

* The input `e` in `linear_combination e` is a linear combination of proofs of equalities,
  given as a sum/difference of coefficients multiplied by expressions.
  The coefficients may be arbitrary expressions.
  The expressions can be arbitrary proof terms proving equalities.
  Most commonly they are hypothesis names `h1, h2, ...`.
* `linear_combination (norm := tac) e` runs the "normalization tactic" `tac`
  on the subgoal(s) after constructing the linear combination.
  * The default normalization tactic is `ring1`, which closes the goal or fails.
  * To get a subgoal in the case that it is not immediately provable, use
    `ring_nf` as the normalization tactic.
  * To avoid normalization entirely, use `skip` as the normalization tactic.
* `linear_combination2 e` is the same as `linear_combination e` but it produces two
  subgoals instead of one: rather than proving that `(a - b) - (a' - b') = 0` where
  `a' = b'` is the linear combination from `e` and `a = b` is the goal,
  it instead attempts to prove `a = a'` and `b = b'`.
  Because it does not use subtraction, this form is applicable also to semirings.
  * Note that a goal which is provable by `linear_combination e` may not be provable
    by `linear_combination2 e`; in general you may need to add a coefficient to `e`
    to make both sides match, as in `linear_combination2 e + c`.
  * You can also reverse equalities using `← h`, so for example if `h₁ : a = b`
    then `2 * (← h)` is a proof of `2 * b = 2 * a`.

Example Usage:
```
example (x y : ℤ) (h1 : x*y + 2*x = 1) (h2 : x = y) : x*y = -2*y + 1 := by
  linear_combination 1*h1 - 2*h2

example (x y : ℤ) (h1 : x*y + 2*x = 1) (h2 : x = y) : x*y = -2*y + 1 := by
  linear_combination h1 - 2*h2

example (x y : ℤ) (h1 : x*y + 2*x = 1) (h2 : x = y) : x*y = -2*y + 1 := by
  linear_combination (norm := ring_nf) -2*h2
  /- Goal: x * y + x * 2 - 1 = 0 -/

example (x y z : ℝ) (ha : x + 2*y - z = 4) (hb : 2*x + y + z = -2)
    (hc : x + 2*y + z = 2) :
    -3*x - 3*y - 4*z = 2 := by
  linear_combination ha - hb - 2*hc

example (x y : ℚ) (h1 : x + y = 3) (h2 : 3*x = 7) :
    x*x*y + y*x*y + 6*x = 3*x*y + 14 := by
  linear_combination x*y*h1 + 2*h2

example (x y : ℤ) (h1 : x = -3) (h2 : y = 10) : 2*x = -6 := by
  linear_combination (norm := skip) 2*h1
  simp

axiom qc : ℚ
axiom hqc : qc = 2*qc

example (a b : ℚ) (h : ∀ p q : ℚ, p = q) : 3*a + qc = 3*b + 2*qc := by
  linear_combination 3 * h a b + hqc
```

# map_tacs
Defined in: `Std.Tactic.«tacticMap_tacs[_;`
»]
Assuming there are `n` goals, `map_tacs [t1; t2; ...; tn]` applies each `ti` to the respective
goal and leaves the resulting subgoals.

# match
Defined in: `Std.Tactic.«tacticMatch_,,With.»`

The syntax `match x with.` is a variant of `nomatch x` which supports pattern matching on multiple
discriminants, like regular `match`, and simply has no alternatives in the match.

# match_target
Defined in: `Mathlib.Tactic.tacticMatch_target_`


# measurability
Defined in: `tacticMeasurability_`

The tactic `measurability` solves goals of the form `Measurable f`, `AEMeasurable f`,
`StronglyMeasurable f`, `AEStronglyMeasurable f μ`, or `MeasurableSet s` by applying lemmas tagged
with the `measurability` user attribute.

# measurability!
Defined in: `measurability!`


# measurability!?
Defined in: `measurability!?`


# measurability?
Defined in: `tacticMeasurability?_`

The tactic `measurability?` solves goals of the form `Measurable f`, `AEMeasurable f`,
`StronglyMeasurable f`, `AEStronglyMeasurable f μ`, or `MeasurableSet s` by applying lemmas tagged
with the `measurability` user attribute, and suggests a faster proof script that can be substituted
for the tactic call in case of success.

# mfld_set_tac
Defined in: `Tactic.MfldSetTac.mfldSetTac`

A very basic tactic to show that sets showing up in manifolds coincide or are included
in one another.

# mod_cases
Defined in: `Mathlib.Tactic.ModCases.«tacticMod_cases_:_%_»`

* The tactic `mod_cases h : e % 3` will perform a case disjunction on `e : ℤ` and yield subgoals
  containing the assumptions `h : e ≡ 0 [ZMOD 3]`, `h : e ≡ 1 [ZMOD 3]`, `h : e ≡ 2 [ZMOD 3]`
  respectively.
* In general, `mod_cases h : e % n` works
  when `n` is a positive numeral and `e` is an expression of type `ℤ`.
* If `h` is omitted as in `mod_cases e % n`, it will be default-named `H`.

# mono
Defined in: `Mathlib.Tactic.Monotonicity.mono`

`mono` applies monotonicity rules and local hypotheses repetitively.  For example,
```lean
example (x y z k : ℤ)
    (h : 3 ≤ (4 : ℤ))
    (h' : z ≤ y) :
    (k + 3 + x) - y ≤ (k + 4 + x) - z := by
  mono
```

# monoidal_coherence
Defined in: `Mathlib.Tactic.Coherence.tacticMonoidal_coherence`

Coherence tactic for monoidal categories.
Use `pure_coherence` instead, which is a frontend to this one.

# next
Defined in: `Lean.Parser.Tactic.«tacticNext_=>_»`

`next => tac` focuses on the next goal and solves it using `tac`, or else fails.
`next x₁ ... xₙ => tac` additionally renames the `n` most recent hypotheses with
inaccessible names to the given names.

# nlinarith
Defined in: `nlinarith`

An extension of `linarith` with some preprocessing to allow it to solve some nonlinear arithmetic
problems. (Based on Coq's `nra` tactic.) See `linarith` for the available syntax of options,
which are inherited by `nlinarith`; that is, `nlinarith!` and `nlinarith only [h1, h2]` all work as
in `linarith`. The preprocessing is as follows:

* For every subterm `a ^ 2` or `a * a` in a hypothesis or the goal,
  the assumption `0 ≤ a ^ 2` or `0 ≤ a * a` is added to the context.
* For every pair of hypotheses `a1 R1 b1`, `a2 R2 b2` in the context, `R1, R2 ∈ {<, ≤, =}`,
  the assumption `0 R' (b1 - a1) * (b2 - a2)` is added to the context (non-recursively),
  where `R ∈ {<, ≤, =}` is the appropriate comparison derived from `R1, R2`.

# nlinarith!
Defined in: `tacticNlinarith!_`

An extension of `linarith` with some preprocessing to allow it to solve some nonlinear arithmetic
problems. (Based on Coq's `nra` tactic.) See `linarith` for the available syntax of options,
which are inherited by `nlinarith`; that is, `nlinarith!` and `nlinarith only [h1, h2]` all work as
in `linarith`. The preprocessing is as follows:

* For every subterm `a ^ 2` or `a * a` in a hypothesis or the goal,
  the assumption `0 ≤ a ^ 2` or `0 ≤ a * a` is added to the context.
* For every pair of hypotheses `a1 R1 b1`, `a2 R2 b2` in the context, `R1, R2 ∈ {<, ≤, =}`,
  the assumption `0 R' (b1 - a1) * (b2 - a2)` is added to the context (non-recursively),
  where `R ∈ {<, ≤, =}` is the appropriate comparison derived from `R1, R2`.

# noncomm_ring
Defined in: `Mathlib.Tactic.NoncommRing.noncomm_ring`

A tactic for simplifying identities in not-necessarily-commutative rings.

An example:
```lean
example {R : Type*} [Ring R] (a b c : R) : a * (b + c + c - b) = 2*a*c :=
by noncomm_ring
```

# nontriviality
Defined in: `Mathlib.Tactic.Nontriviality.nontriviality`

Attempts to generate a `Nontrivial α` hypothesis.

The tactic first looks for an instance using `infer_instance`.

If the goal is an (in)equality, the type `α` is inferred from the goal.
Otherwise, the type needs to be specified in the tactic invocation, as `nontriviality α`.

The `nontriviality` tactic will first look for strict inequalities amongst the hypotheses,
and use these to derive the `Nontrivial` instance directly.

Otherwise, it will perform a case split on `Subsingleton α ∨ Nontrivial α`, and attempt to discharge
the `Subsingleton` goal using `simp [h₁, h₂, ..., hₙ, nontriviality]`, where `[h₁, h₂, ..., hₙ]` is
a list of additional `simp` lemmas that can be passed to `nontriviality` using the syntax
`nontriviality α using h₁, h₂, ..., hₙ`.

```
example {R : Type} [OrderedRing R] {a : R} (h : 0 < a) : 0 < a := by
  nontriviality -- There is now a `nontrivial R` hypothesis available.
  assumption
```

```
example {R : Type} [CommRing R] {r s : R} : r * s = s * r := by
  nontriviality -- There is now a `nontrivial R` hypothesis available.
  apply mul_comm
```

```
example {R : Type} [OrderedRing R] {a : R} (h : 0 < a) : (2 : ℕ) ∣ 4 := by
  nontriviality R -- there is now a `nontrivial R` hypothesis available.
  dec_trivial
```

```
def myeq {α : Type} (a b : α) : Prop := a = b

example {α : Type} (a b : α) (h : a = b) : myeq a b := by
  success_if_fail nontriviality α -- Fails
  nontriviality α using myeq -- There is now a `nontrivial α` hypothesis available
  assumption
```

# norm_cast
Defined in: `Tactic.NormCast.tacticNorm_cast_`

Normalize casts at the given locations by moving them "upwards".

# norm_cast0
Defined in: `Tactic.NormCast.tacticNorm_cast0_`


# norm_num
Defined in: `Mathlib.Tactic.normNum`

Normalize numerical expressions. Supports the operations `+` `-` `*` `/` `⁻¹` `^` and `%`
over numerical types such as `ℕ`, `ℤ`, `ℚ`, `ℝ`, `ℂ` and some general algebraic types,
and can prove goals of the form `A = B`, `A ≠ B`, `A < B` and `A ≤ B`, where `A` and `B` are
numerical expressions. It also has a relatively simple primality prover.

# norm_num1
Defined in: `Mathlib.Tactic.normNum1`

Basic version of `norm_num` that does not call `simp`.

# nth_rewrite
Defined in: `Mathlib.Tactic.nthRewriteSeq`

`nth_rewrite` is a variant of `rewrite` that only changes the nth occurrence of the expression
to be rewritten.

Note: The occurrences are counted beginning with `1` and not `0`, this is different than in
mathlib3. The translation will be handled by mathport.

# nth_rw
Defined in: `Mathlib.Tactic.nthRwSeq`

`nth_rw` is like `nth_rewrite`, but also tries to close the goal by trying `rfl` afterwards.

# observe
Defined in: `Mathlib.Tactic.LibrarySearch.observe`

`observe hp : p` asserts the proposition `p`, and tries to prove it using `exact?`.
If no proof is found, the tactic fails.
In other words, this tactic is equivalent to `have hp : p := by exact?`.

If `hp` is omitted, then the placeholder `this` is used.

The variant `observe? hp : p` will emit a trace message of the form `have hp : p := proof_term`.
This may be particularly useful to speed up proofs.

# observe?
Defined in: `Mathlib.Tactic.LibrarySearch.«tacticObserve?__:_Using__,,»`

`observe hp : p` asserts the proposition `p`, and tries to prove it using `exact?`.
If no proof is found, the tactic fails.
In other words, this tactic is equivalent to `have hp : p := by exact?`.

If `hp` is omitted, then the placeholder `this` is used.

The variant `observe? hp : p` will emit a trace message of the form `have hp : p := proof_term`.
This may be particularly useful to speed up proofs.

# observe?
Defined in: `Mathlib.Tactic.LibrarySearch.«tacticObserve?__:_»`

`observe hp : p` asserts the proposition `p`, and tries to prove it using `exact?`.
If no proof is found, the tactic fails.
In other words, this tactic is equivalent to `have hp : p := by exact?`.

If `hp` is omitted, then the placeholder `this` is used.

The variant `observe? hp : p` will emit a trace message of the form `have hp : p := proof_term`.
This may be particularly useful to speed up proofs.

# obtain
Defined in: `Std.Tactic.obtain`

The `obtain` tactic is a combination of `have` and `rcases`. See `rcases` for
a description of supported patterns.

```lean
obtain ⟨patt⟩ : type := proof
```
is equivalent to
```lean
have h : type := proof
rcases h with ⟨patt⟩
```

If `⟨patt⟩` is omitted, `rcases` will try to infer the pattern.

If `type` is omitted, `:= proof` is required.

# on_goal
Defined in: `Mathlib.Tactic.«tacticOn_goal-_=>_»`

`on_goal n => tacSeq` creates a block scope for the `n`-th goal and tries the sequence
of tactics `tacSeq` on it.

`on_goal -n => tacSeq` does the same, but the `n`-th goal is chosen by counting from the
bottom.

The goal is not required to be solved and any resulting subgoals are inserted back into the
list of goals, replacing the chosen goal.

# on_goal
Defined in: `Aesop.Parser.onGoal`


# pick_goal
Defined in: `Mathlib.Tactic.«tacticPick_goal-_»`

`pick_goal n` will move the `n`-th goal to the front.

`pick_goal -n` will move the `n`-th goal (counting from the bottom) to the front.

See also `Tactic.rotate_goals`, which moves goals from the front to the back and vice-versa.

# polyrith
Defined in: `Mathlib.Tactic.Polyrith.«tacticPolyrithOnly[_`
»]
Attempts to prove polynomial equality goals through polynomial arithmetic
on the hypotheses (and additional proof terms if the user specifies them).
It proves the goal by generating an appropriate call to the tactic
`linear_combination`. If this call succeeds, the call to `linear_combination`
is suggested to the user.

* `polyrith` will use all relevant hypotheses in the local context.
* `polyrith [t1, t2, t3]` will add proof terms t1, t2, t3 to the local context.
* `polyrith only [h1, h2, h3, t1, t2, t3]` will use only local hypotheses
  `h1`, `h2`, `h3`, and proofs `t1`, `t2`, `t3`. It will ignore the rest of the local context.

Notes:
* This tactic only works with a working internet connection, since it calls Sage
  using the SageCell web API at <https://sagecell.sagemath.org/>.
  Many thanks to the Sage team and organization for allowing this use.
* This tactic assumes that the user has `python3` installed and available on the path.
  (Test by opening a terminal and executing `python3 --version`.)
  It also assumes that the `requests` library is installed: `python3 -m pip install requests`.

Examples:

```lean
example (x y : ℚ) (h1 : x*y + 2*x = 1) (h2 : x = y) :
  x*y = -2*y + 1 :=
by polyrith
-- Try this: linear_combination h1 - 2 * h2

example (x y z w : ℚ) (hzw : z = w) : x*z + 2*y*z = x*w + 2*y*w :=
by polyrith
-- Try this: linear_combination (2 * y + x) * hzw

constant scary : ∀ a b : ℚ, a + b = 0

example (a b c d : ℚ) (h : a + b = 0) (h2: b + c = 0) : a + b + c + d = 0 :=
by polyrith only [scary c d, h]
-- Try this: linear_combination scary c d + h
```

# positivity
Defined in: `Mathlib.Tactic.Positivity.positivity`

Tactic solving goals of the form `0 ≤ x`, `0 < x` and `x ≠ 0`.  The tactic works recursively
according to the syntax of the expression `x`, if the atoms composing the expression all have
numeric lower bounds which can be proved positive/nonnegative/nonzero by `norm_num`.  This tactic
either closes the goal or fails.

Examples:
```
example {a : ℤ} (ha : 3 < a) : 0 ≤ a ^ 3 + a := by positivity

example {a : ℤ} (ha : 1 < a) : 0 < |(3:ℤ) + a| := by positivity

example {b : ℤ} : 0 ≤ max (-3) (b ^ 2) := by positivity
```

# pure_coherence
Defined in: `Mathlib.Tactic.Coherence.pure_coherence`

`pure_coherence` uses the coherence theorem for monoidal categories to prove the goal.
It can prove any equality made up only of associators, unitors, and identities.
```lean
example {C : Type} [Category C] [MonoidalCategory C] :
  (λ_ (𝟙_ C)).hom = (ρ_ (𝟙_ C)).hom :=
by pure_coherence
```

Users will typically just use the `coherence` tactic,
which can also cope with identities of the form
`a ≫ f ≫ b ≫ g ≫ c = a' ≫ f ≫ b' ≫ g ≫ c'`
where `a = a'`, `b = b'`, and `c = c'` can be proved using `pure_coherence`

# push_cast
Defined in: `Tactic.NormCast.pushCast`


# push_neg
Defined in: `Mathlib.Tactic.PushNeg.tacticPush_neg_`

Push negations into the conclusion of a hypothesis.
For instance, a hypothesis `h : ¬ ∀ x, ∃ y, x ≤ y` will be transformed by `push_neg at h` into
`h : ∃ x, ∀ y, y < x`. Variable names are conserved.
This tactic pushes negations inside expressions. For instance, given a hypothesis
```lean
h : ¬ ∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| ≤ δ → |f x - y₀| ≤ ε)
```
writing `push_neg at h` will turn `h` into
```lean
h : ∃ ε, ε > 0 ∧ ∀ δ, δ > 0 → (∃ x, |x - x₀| ≤ δ ∧ ε < |f x - y₀|),
```
(The pretty printer does *not* use the abbreviations `∀ δ > 0` and `∃ ε > 0` but this issue
has nothing to do with `push_neg`).

Note that names are conserved by this tactic, contrary to what would happen with `simp`
using the relevant lemmas. One can also use this tactic at the goal using `push_neg`,
at every hypothesis and the goal using `push_neg at *` or at selected hypotheses and the goal
using say `push_neg at h h' ⊢` as usual.

This tactic has two modes: in standard mode, it transforms `¬(p ∧ q)` into `p → ¬q`, whereas in
distrib mode it produces `¬p ∨ ¬q`. To use distrib mode, use `set_option push_neg.use_distrib true`.

# qify
Defined in: `Mathlib.Tactic.Qify.qify`

The `qify` tactic is used to shift propositions from `ℕ` or `ℤ` to `ℚ`.
This is often useful since `ℚ` has well-behaved division.
```
example (a b c x y z : ℕ) (h : ¬ x*y*z < 0) : c < a + 3*b := by
  qify
  qify at h
  /-
  h : ¬↑x * ↑y * ↑z < 0
  ⊢ ↑c < ↑a + 3 * ↑b
  -/
  sorry
```
`qify` can be given extra lemmas to use in simplification. This is especially useful in the
presence of nat subtraction: passing `≤` arguments will allow `push_cast` to do more work.
```
example (a b c : ℤ) (h : a / b = c) (hab : b ∣ a) (hb : b ≠ 0) : a = c * b := by
  qify [hab] at h hb ⊢
  exact (div_eq_iff hb).1 h
```
`qify` makes use of the `@[zify_simps]` and `@[qify_simps]` attributes to move propositions,
and the `push_cast` tactic to simplify the `ℚ`-valued expressions.

# rcases
Defined in: `Std.Tactic.rcases`

`rcases` is a tactic that will perform `cases` recursively, according to a pattern. It is used to
destructure hypotheses or expressions composed of inductive types like `h1 : a ∧ b ∧ c ∨ d` or
`h2 : ∃ x y, trans_rel R x y`. Usual usage might be `rcases h1 with ⟨ha, hb, hc⟩ | hd` or
`rcases h2 with ⟨x, y, _ | ⟨z, hxz, hzy⟩⟩` for these examples.

Each element of an `rcases` pattern is matched against a particular local hypothesis (most of which
are generated during the execution of `rcases` and represent individual elements destructured from
the input expression). An `rcases` pattern has the following grammar:

* A name like `x`, which names the active hypothesis as `x`.
* A blank `_`, which does nothing (letting the automatic naming system used by `cases` name the
  hypothesis).
* A hyphen `-`, which clears the active hypothesis and any dependents.
* The keyword `rfl`, which expects the hypothesis to be `h : a = b`, and calls `subst` on the
  hypothesis (which has the effect of replacing `b` with `a` everywhere or vice versa).
* A type ascription `p : ty`, which sets the type of the hypothesis to `ty` and then matches it
  against `p`. (Of course, `ty` must unify with the actual type of `h` for this to work.)
* A tuple pattern `⟨p1, p2, p3⟩`, which matches a constructor with many arguments, or a series
  of nested conjunctions or existentials. For example if the active hypothesis is `a ∧ b ∧ c`,
  then the conjunction will be destructured, and `p1` will be matched against `a`, `p2` against `b`
  and so on.
* A `@` before a tuple pattern as in `@⟨p1, p2, p3⟩` will bind all arguments in the constructor,
  while leaving the `@` off will only use the patterns on the explicit arguments.
* An alteration pattern `p1 | p2 | p3`, which matches an inductive type with multiple constructors,
  or a nested disjunction like `a ∨ b ∨ c`.

A pattern like `⟨a, b, c⟩ | ⟨d, e⟩` will do a split over the inductive datatype,
naming the first three parameters of the first constructor as `a,b,c` and the
first two of the second constructor `d,e`. If the list is not as long as the
number of arguments to the constructor or the number of constructors, the
remaining variables will be automatically named. If there are nested brackets
such as `⟨⟨a⟩, b | c⟩ | d` then these will cause more case splits as necessary.
If there are too many arguments, such as `⟨a, b, c⟩` for splitting on
`∃ x, ∃ y, p x`, then it will be treated as `⟨a, ⟨b, c⟩⟩`, splitting the last
parameter as necessary.

`rcases` also has special support for quotient types: quotient induction into Prop works like
matching on the constructor `quot.mk`.

`rcases h : e with PAT` will do the same as `rcases e with PAT` with the exception that an
assumption `h : e = PAT` will be added to the context.

# rcongr
Defined in: `Std.Tactic.rcongr`

Repeatedly apply `congr` and `ext`, using the given patterns as arguments for `ext`.

There are two ways this tactic stops:
* `congr` fails (makes no progress), after having already applied `ext`.
* `congr` canceled out the last usage of `ext`. In this case, the state is reverted to before
  the `congr` was applied.

For example, when the goal is
```
⊢ (fun x => f x + 3) '' s = (fun x => g x + 3) '' s
```
then `rcongr x` produces the goal
```
x : α ⊢ f x = g x
```
This gives the same result as `congr; ext x; congr`.

In contrast, `congr` would produce
```
⊢ (fun x => f x + 3) = (fun x => g x + 3)
```
and `congr with x` (or `congr; ext x`) would produce
```
x : α ⊢ f x + 3 = g x + 3
```

# recover
Defined in: `Mathlib.Tactic.tacticRecover_`

Modifier `recover` for a tactic (sequence) to debug cases where goals are closed incorrectly.
The tactic `recover tacs` for a tactic (sequence) tacs applies the tactics and then adds goals
that are not closed starting from the original

# reduce
Defined in: `Mathlib.Tactic.tacticReduce__`

`reduce at loc` completely reduces the given location.
This also exists as a `conv`-mode tactic.

This does the same transformation as the `#reduce` command.

# refine
Defined in: `Lean.Parser.Tactic.refine`

`refine e` behaves like `exact e`, except that named (`?x`) or unnamed (`?_`)
holes in `e` that are not solved by unification with the main goal's target type
are converted into new goals, using the hole's name, if any, as the goal case name.

# refine'
Defined in: `Lean.Parser.Tactic.refine'`

`refine' e` behaves like `refine e`, except that unsolved placeholders (`_`)
and implicit parameters are also converted into new goals.

# refine_lift
Defined in: `Lean.Parser.Tactic.tacticRefine_lift_`

Auxiliary macro for lifting have/suffices/let/...
It makes sure the "continuation" `?_` is the main goal after refining.

# refine_lift'
Defined in: `Lean.Parser.Tactic.tacticRefine_lift'_`

Similar to `refine_lift`, but using `refine'`

# rel
Defined in: `Mathlib.Tactic.GCongr.«tacticRel[_`
»]
The `rel` tactic applies "generalized congruence" rules to solve a relational goal by
"substitution".  For example,
```
example {a b x c d : ℝ} (h1 : a ≤ b) (h2 : c ≤ d) :
    x ^ 2 * a + c ≤ x ^ 2 * b + d := by
  rel [h1, h2]
```
In this example we "substitute" the hypotheses `a ≤ b` and `c ≤ d` into the LHS `x ^ 2 * a + c` of
the goal and obtain the RHS `x ^ 2 * b + d`, thus proving the goal.

The "generalized congruence" rules used are the library lemmas which have been tagged with the
attribute `@[gcongr]`.  For example, the first example constructs the proof term
```
add_le_add (mul_le_mul_of_nonneg_left h1 (pow_bit0_nonneg x 1)) h2
```
using the generalized congruence lemmas `add_le_add` and `mul_le_mul_of_nonneg_left`.  If there are
no applicable generalized congruence lemmas, the tactic fails.

The tactic attempts to discharge side goals to these "generalized congruence" lemmas (such as the
side goal `0 ≤ x ^ 2` in the above application of `mul_le_mul_of_nonneg_left`) using the tactic
`gcongr_discharger`, which wraps `positivity` but can also be extended. If the side goals cannot
be discharged in this way, the tactic fails.

# rename
Defined in: `Lean.Parser.Tactic.rename`

`rename t => x` renames the most recent hypothesis whose type matches `t`
(which may contain placeholders) to `x`, or fails if no such hypothesis could be found.

# rename'
Defined in: `Mathlib.Tactic.rename'`

`rename' h => hnew` renames the hypothesis named `h` to `hnew`.
To rename several hypothesis, use `rename' h₁ => h₁new, h₂ => h₂new`.
You can use `rename' a => b, b => a` to swap two variables.

# rename_bvar
Defined in: `Mathlib.Tactic.«tacticRename_bvar_→__»`

* `rename_bvar old new` renames all bound variables named `old` to `new` in the target.
* `rename_bvar old new at h` does the same in hypothesis `h`.

```lean
example (P : ℕ → ℕ → Prop) (h : ∀ n, ∃ m, P n m) : ∀ l, ∃ m, P l m :=
begin
  rename_bvar n q at h, -- h is now ∀ (q : ℕ), ∃ (m : ℕ), P q m,
  rename_bvar m n, -- target is now ∀ (l : ℕ), ∃ (n : ℕ), P k n,
  exact h -- Lean does not care about those bound variable names
end
```
Note: name clashes are resolved automatically.

# rename_i
Defined in: `Lean.Parser.Tactic.renameI`

`rename_i x_1 ... x_n` renames the last `n` inaccessible names using the given names.

# repeat
Defined in: `Lean.Parser.Tactic.tacticRepeat_`

`repeat tac` repeatedly applies `tac` to the main goal until it fails.
That is, if `tac` produces multiple subgoals, only subgoals up to the first failure will be visited.
The `Std` library provides `repeat'` which repeats separately in each subgoal.

# repeat'
Defined in: `Std.Tactic.tacticRepeat'_`

`repeat' tac` runs `tac` on all of the goals to produce a new list of goals,
then runs `tac` again on all of those goals, and repeats until `tac` fails on all remaining goals.

# repeat1
Defined in: `Std.Tactic.tacticRepeat1_`

`repeat1 tac` applies `tac` to main goal at least once. If the application succeeds,
the tactic is applied recursively to the generated subgoals until it eventually fails.

# repeat1
Defined in: `Mathlib.Tactic.tacticRepeat1_`

`repeat1 tac` applies `tac` to main goal at least once. If the application succeeds,
the tactic is applied recursively to the generated subgoals until it eventually fails.

# replace
Defined in: `Mathlib.Tactic.replace'`

Acts like `have`, but removes a hypothesis with the same name as
this one if possible. For example, if the state is:

Then after `replace h : β` the state will be:

```lean
case h
f : α → β
h : α
⊢ β

f : α → β
h : β
⊢ goal
```

whereas `have h : β` would result in:

```lean
case h
f : α → β
h : α
⊢ β

f : α → β
h✝ : α
h : β
⊢ goal
```

# replace
Defined in: `Std.Tactic.tacticReplace_`

Acts like `have`, but removes a hypothesis with the same name as
this one if possible. For example, if the state is:

```lean
f : α → β
h : α
⊢ goal
```

Then after `replace h := f h` the state will be:

```lean
f : α → β
h : β
⊢ goal
```

whereas `have h := f h` would result in:

```lean
f : α → β
h† : α
h : β
⊢ goal
```

This can be used to simulate the `specialize` and `apply at` tactics of Coq.

# revert
Defined in: `Lean.Parser.Tactic.revert`

`revert x...` is the inverse of `intro x...`: it moves the given hypotheses
into the main goal's target type.

# rewrite
Defined in: `Lean.Parser.Tactic.rewriteSeq`

`rewrite [e]` applies identity `e` as a rewrite rule to the target of the main goal.
If `e` is preceded by left arrow (`←` or `<-`), the rewrite is applied in the reverse direction.
If `e` is a defined constant, then the equational theorems associated with `e` are used.
This provides a convenient way to unfold `e`.
- `rewrite [e₁, ..., eₙ]` applies the given rules sequentially.
- `rewrite [e] at l` rewrites `e` at location(s) `l`, where `l` is either `*` or a
  list of hypotheses in the local context. In the latter case, a turnstile `⊢` or `|-`
  can also be used, to signify the target of the goal.

# rfl
Defined in: `Lean.Parser.Tactic.tacticRfl`

`rfl` tries to close the current goal using reflexivity.
This is supposed to be an extensible tactic and users can add their own support
for new reflexive relations.

# rfl'
Defined in: `Lean.Parser.Tactic.tacticRfl'`

`rfl'` is similar to `rfl`, but disables smart unfolding and unfolds all kinds of definitions,
theorems included (relevant for declarations defined by well-founded recursion).

# right
Defined in: `Mathlib.Tactic.tacticRight`


# ring
Defined in: `Mathlib.Tactic.RingNF.ring`

Tactic for evaluating expressions in *commutative* (semi)rings, allowing for variables in the
exponent.

* `ring!` will use a more aggressive reducibility setting to determine equality of atoms.
* `ring1` fails if the target is not an equality.

For example:
```
example (n : ℕ) (m : ℤ) : 2^(n+1) * m = 2 * 2^n * m := by ring
example (a b : ℤ) (n : ℕ) : (a + b)^(n + 2) = (a^2 + b^2 + a * b + b * a) * (a + b)^n := by ring
example (x y : ℕ) : x + id y = y + id x := by ring!
```

# ring!
Defined in: `Mathlib.Tactic.RingNF.tacticRing!`

Tactic for evaluating expressions in *commutative* (semi)rings, allowing for variables in the
exponent.

* `ring!` will use a more aggressive reducibility setting to determine equality of atoms.
* `ring1` fails if the target is not an equality.

For example:
```
example (n : ℕ) (m : ℤ) : 2^(n+1) * m = 2 * 2^n * m := by ring
example (a b : ℤ) (n : ℕ) : (a + b)^(n + 2) = (a^2 + b^2 + a * b + b * a) * (a + b)^n := by ring
example (x y : ℕ) : x + id y = y + id x := by ring!
```

# ring1
Defined in: `Mathlib.Tactic.Ring.ring1`

Tactic for solving equations of *commutative* (semi)rings,
allowing variables in the exponent.

* This version of `ring` fails if the target is not an equality.
* The variant `ring1!` will use a more aggressive reducibility setting
  to determine equality of atoms.

# ring1!
Defined in: `Mathlib.Tactic.Ring.tacticRing1!`

Tactic for solving equations of *commutative* (semi)rings,
allowing variables in the exponent.

* This version of `ring` fails if the target is not an equality.
* The variant `ring1!` will use a more aggressive reducibility setting
  to determine equality of atoms.

# ring1_nf
Defined in: `Mathlib.Tactic.RingNF.ring1NF`

Tactic for solving equations of *commutative* (semi)rings, allowing variables in the exponent.

* This version of `ring1` uses `ring_nf` to simplify in atoms.
* The variant `ring1_nf!` will use a more aggressive reducibility setting
  to determine equality of atoms.

# ring1_nf!
Defined in: `Mathlib.Tactic.RingNF.tacticRing1_nf!_`

Tactic for solving equations of *commutative* (semi)rings, allowing variables in the exponent.

* This version of `ring1` uses `ring_nf` to simplify in atoms.
* The variant `ring1_nf!` will use a more aggressive reducibility setting
  to determine equality of atoms.

# ring_nf
Defined in: `Mathlib.Tactic.RingNF.ringNF`

Simplification tactic for expressions in the language of commutative (semi)rings,
which rewrites all ring expressions into a normal form.
* `ring_nf!` will use a more aggressive reducibility setting to identify atoms.
* `ring_nf (config := cfg)` allows for additional configuration:
  * `red`: the reducibility setting (overridden by `!`)
  * `recursive`: if true, `ring_nf` will also recurse into atoms
* `ring_nf` works as both a tactic and a conv tactic.
  In tactic mode, `ring_nf at h` can be used to rewrite in a hypothesis.

# ring_nf!
Defined in: `Mathlib.Tactic.RingNF.tacticRing_nf!__`

Simplification tactic for expressions in the language of commutative (semi)rings,
which rewrites all ring expressions into a normal form.
* `ring_nf!` will use a more aggressive reducibility setting to identify atoms.
* `ring_nf (config := cfg)` allows for additional configuration:
  * `red`: the reducibility setting (overridden by `!`)
  * `recursive`: if true, `ring_nf` will also recurse into atoms
* `ring_nf` works as both a tactic and a conv tactic.
  In tactic mode, `ring_nf at h` can be used to rewrite in a hypothesis.

# rintro
Defined in: `Std.Tactic.rintro`

The `rintro` tactic is a combination of the `intros` tactic with `rcases` to
allow for destructuring patterns while introducing variables. See `rcases` for
a description of supported patterns. For example, `rintro (a | ⟨b, c⟩) ⟨d, e⟩`
will introduce two variables, and then do case splits on both of them producing
two subgoals, one with variables `a d e` and the other with `b c d e`.

`rintro`, unlike `rcases`, also supports the form `(x y : ty)` for introducing
and type-ascripting multiple variables at once, similar to binders.

# rotate_left
Defined in: `Lean.Parser.Tactic.rotateLeft`

`rotate_left n` rotates goals to the left by `n`. That is, `rotate_left 1`
takes the main goal and puts it to the back of the subgoal list.
If `n` is omitted, it defaults to `1`.

# rotate_right
Defined in: `Lean.Parser.Tactic.rotateRight`

Rotate the goals to the right by `n`. That is, take the goal at the back
and push it to the front `n` times. If `n` is omitted, it defaults to `1`.

# rsuffices
Defined in: `rsuffices`

The `rsuffices` tactic is an alternative version of `suffices`, that allows the usage
of any syntax that would be valid in an `obtain` block. This tactic just calls `obtain`
on the expression, and then `rotate_left`.

# run_tac
Defined in: `Mathlib.RunCmd.runTac`

The `run_tac doSeq` tactic executes code in `TacticM Unit`.

# rw
Defined in: `Lean.Parser.Tactic.rwSeq`

`rw` is like `rewrite`, but also tries to close the goal by "cheap" (reducible) `rfl` afterwards.

# rw!?
Defined in: `Mathlib.Tactic.Rewrites.tacticRw!?__`

`rw?` tries to find a lemma which can rewrite the goal.

`rw?` should not be left in proofs; it is a search tool, like `apply?`.

Suggestions are printed as `rw [h]` or `rw [←h]`.
`rw?!` is the "I'm feeling lucky" mode, and will run the first rewrite it finds.

# rw?
Defined in: `Mathlib.Tactic.Rewrites.rewrites'`

`rw?` tries to find a lemma which can rewrite the goal.

`rw?` should not be left in proofs; it is a search tool, like `apply?`.

Suggestions are printed as `rw [h]` or `rw [←h]`.
`rw?!` is the "I'm feeling lucky" mode, and will run the first rewrite it finds.

# rw?!
Defined in: `Mathlib.Tactic.Rewrites.tacticRw?!__`

`rw?` tries to find a lemma which can rewrite the goal.

`rw?` should not be left in proofs; it is a search tool, like `apply?`.

Suggestions are printed as `rw [h]` or `rw [←h]`.
`rw?!` is the "I'm feeling lucky" mode, and will run the first rewrite it finds.

# rw_mod_cast
Defined in: `Tactic.NormCast.tacticRw_mod_cast___`

Rewrite with the given rules and normalize casts between steps.

# rwa
Defined in: `Std.Tactic.tacticRwa__`

`rwa` calls `rw`, then closes any remaining goals using `assumption`.

# save
Defined in: `Lean.Parser.Tactic.save`

`save` is defined to be the same as `skip`, but the elaborator has
special handling for occurrences of `save` in tactic scripts and will transform
`by tac1; save; tac2` to `by (checkpoint tac1); tac2`, meaning that the effect of `tac1`
will be cached and replayed. This is useful for improving responsiveness
when working on a long tactic proof, by using `save` after expensive tactics.

(TODO: do this automatically and transparently so that users don't have to use
this combinator explicitly.)

# set
Defined in: `Mathlib.Tactic.setTactic`


# set!
Defined in: `Mathlib.Tactic.tacticSet!_`


# show
Defined in: `Lean.Parser.Tactic.tacticShow_`

`show t` finds the first goal whose target unifies with `t`. It makes that the main goal,
performs the unification, and replaces the target with the unified version of `t`.

# show_term
Defined in: `Std.Tactic.showTermTac`

`show_term tac` runs `tac`, then prints the generated term in the form
"exact X Y Z" or "refine X ?_ Z" if there are remaining subgoals.

(For some tactics, the printed term will not be human readable.)

# simp
Defined in: `Lean.Parser.Tactic.simp`

The `simp` tactic uses lemmas and hypotheses to simplify the main goal target or
non-dependent hypotheses. It has many variants:
- `simp` simplifies the main goal target using lemmas tagged with the attribute `[simp]`.
- `simp [h₁, h₂, ..., hₙ]` simplifies the main goal target using the lemmas tagged
  with the attribute `[simp]` and the given `hᵢ`'s, where the `hᵢ`'s are expressions.
  If an `hᵢ` is a defined constant `f`, then the equational lemmas associated with
  `f` are used. This provides a convenient way to unfold `f`.
- `simp [*]` simplifies the main goal target using the lemmas tagged with the
  attribute `[simp]` and all hypotheses.
- `simp only [h₁, h₂, ..., hₙ]` is like `simp [h₁, h₂, ..., hₙ]` but does not use `[simp]` lemmas.
- `simp [-id₁, ..., -idₙ]` simplifies the main goal target using the lemmas tagged
  with the attribute `[simp]`, but removes the ones named `idᵢ`.
- `simp at h₁ h₂ ... hₙ` simplifies the hypotheses `h₁ : T₁` ... `hₙ : Tₙ`. If
  the target or another hypothesis depends on `hᵢ`, a new simplified hypothesis
  `hᵢ` is introduced, but the old one remains in the local context.
- `simp at *` simplifies all the hypotheses and the target.
- `simp [*] at *` simplifies target and all (propositional) hypotheses using the
  other hypotheses.

# simp!
Defined in: `Lean.Parser.Tactic.simpAutoUnfold`

`simp!` is shorthand for `simp` with `autoUnfold := true`.
This will rewrite with all equation lemmas, which can be used to
partially evaluate many definitions.

# simp?
Defined in: `Std.Tactic.simpTrace`

`simp?` takes the same arguments as `simp`, but reports an equivalent call to `simp only`
that would be sufficient to close the goal. This is useful for reducing the size of the simp
set in a local invocation to speed up processing.
```
example (x : Nat) : (if True then x + 2 else 3) = x + 2 := by
  simp? -- prints "Try this: simp only [ite_true]"
```

This command can also be used in `simp_all` and `dsimp`.

# simp?!
Defined in: `Std.Tactic.tacticSimp?!_`

`simp?` takes the same arguments as `simp`, but reports an equivalent call to `simp only`
that would be sufficient to close the goal. This is useful for reducing the size of the simp
set in a local invocation to speed up processing.
```
example (x : Nat) : (if True then x + 2 else 3) = x + 2 := by
  simp? -- prints "Try this: simp only [ite_true]"
```

This command can also be used in `simp_all` and `dsimp`.

# simp_all
Defined in: `Lean.Parser.Tactic.simpAll`

`simp_all` is a stronger version of `simp [*] at *` where the hypotheses and target
are simplified multiple times until no simplication is applicable.
Only non-dependent propositional hypotheses are considered.

# simp_all!
Defined in: `Lean.Parser.Tactic.simpAllAutoUnfold`

`simp_all!` is shorthand for `simp_all` with `autoUnfold := true`.
This will rewrite with all equation lemmas, which can be used to
partially evaluate many definitions.

# simp_all?
Defined in: `Std.Tactic.simpAllTrace`

`simp?` takes the same arguments as `simp`, but reports an equivalent call to `simp only`
that would be sufficient to close the goal. This is useful for reducing the size of the simp
set in a local invocation to speed up processing.
```
example (x : Nat) : (if True then x + 2 else 3) = x + 2 := by
  simp? -- prints "Try this: simp only [ite_true]"
```

This command can also be used in `simp_all` and `dsimp`.

# simp_all?!
Defined in: `Std.Tactic.tacticSimp_all?!_`

`simp?` takes the same arguments as `simp`, but reports an equivalent call to `simp only`
that would be sufficient to close the goal. This is useful for reducing the size of the simp
set in a local invocation to speed up processing.
```
example (x : Nat) : (if True then x + 2 else 3) = x + 2 := by
  simp? -- prints "Try this: simp only [ite_true]"
```

This command can also be used in `simp_all` and `dsimp`.

# simp_all_arith
Defined in: `Lean.Parser.Tactic.simpAllArith`

`simp_all_arith` combines the effects of `simp_all` and `simp_arith`.

# simp_all_arith!
Defined in: `Lean.Parser.Tactic.simpAllArithAutoUnfold`

`simp_all_arith!` combines the effects of `simp_all`, `simp_arith` and `simp!`.

# simp_arith
Defined in: `Lean.Parser.Tactic.simpArith`

`simp_arith` is shorthand for `simp` with `arith := true`.
This enables the use of normalization by linear arithmetic.

# simp_arith!
Defined in: `Lean.Parser.Tactic.simpArithAutoUnfold`

`simp_arith!` is shorthand for `simp_arith` with `autoUnfold := true`.
This will rewrite with all equation lemmas, which can be used to
partially evaluate many definitions.

# simp_intro
Defined in: `Mathlib.Tactic.«tacticSimp_intro_____..Only_»`

The `simp_intro` tactic is a combination of `simp` and `intro`: it will simplify the types of
variables as it introduces them and uses the new variables to simplify later arguments
and the goal.
* `simp_intro x y z` introduces variables named `x y z`
* `simp_intro x y z ..` introduces variables named `x y z` and then keeps introducing `_` binders
* `simp_intro (config := cfg) (discharger := tac) x y .. only [h₁, h₂]`:
  `simp_intro` takes the same options as `simp` (see `simp`)
```
example : x + 0 = y → x = z := by
  simp_intro h
  -- h: x = y ⊢ y = z
  sorry
```

# simp_rw
Defined in: `Mathlib.Tactic.tacticSimp_rw__`

`simp_rw` functions as a mix of `simp` and `rw`. Like `rw`, it applies each
rewrite rule in the given order, but like `simp` it repeatedly applies these
rules and also under binders like `∀ x, ...`, `∃ x, ...` and `λ x, ...`.
Usage:

- `simp_rw [lemma_1, ..., lemma_n]` will rewrite the goal by applying the
  lemmas in that order. A lemma preceded by `←` is applied in the reverse direction.
- `simp_rw [lemma_1, ..., lemma_n] at h₁ ... hₙ` will rewrite the given hypotheses.
- `simp_rw [...] at *` rewrites in the whole context: all hypotheses and the goal.

Lemmas passed to `simp_rw` must be expressions that are valid arguments to `simp`.
For example, neither `simp` nor `rw` can solve the following, but `simp_rw` can:

```lean
example {a : ℕ}
  (h1 : ∀ a b : ℕ, a - 1 ≤ b ↔ a ≤ b + 1)
  (h2 : ∀ a b : ℕ, a ≤ b ↔ ∀ c, c < a → c < b) :
  (∀ b, a - 1 ≤ b) = ∀ b c : ℕ, c < a → c < b + 1 :=
by simp_rw [h1, h2]
```

# simp_wf
Defined in: `tacticSimp_wf`

Unfold definitions commonly used in well founded relation definitions.
This is primarily intended for internal use in `decreasing_tactic`.

# simpa
Defined in: `Std.Tactic.Simpa.simpa`

This is a "finishing" tactic modification of `simp`. It has two forms.

* `simpa [rules, ⋯] using e` will simplify the goal and the type of
`e` using `rules`, then try to close the goal using `e`.

Simplifying the type of `e` makes it more likely to match the goal
(which has also been simplified). This construction also tends to be
more robust under changes to the simp lemma set.

* `simpa [rules, ⋯]` will simplify the goal and the type of a
hypothesis `this` if present in the context, then try to close the goal using
the `assumption` tactic.

#TODO: implement `?`

# simpa!
Defined in: `Std.Tactic.Simpa.tacticSimpa!_`

This is a "finishing" tactic modification of `simp`. It has two forms.

* `simpa [rules, ⋯] using e` will simplify the goal and the type of
`e` using `rules`, then try to close the goal using `e`.

Simplifying the type of `e` makes it more likely to match the goal
(which has also been simplified). This construction also tends to be
more robust under changes to the simp lemma set.

* `simpa [rules, ⋯]` will simplify the goal and the type of a
hypothesis `this` if present in the context, then try to close the goal using
the `assumption` tactic.

#TODO: implement `?`

# simpa?
Defined in: `Std.Tactic.Simpa.tacticSimpa?_`

This is a "finishing" tactic modification of `simp`. It has two forms.

* `simpa [rules, ⋯] using e` will simplify the goal and the type of
`e` using `rules`, then try to close the goal using `e`.

Simplifying the type of `e` makes it more likely to match the goal
(which has also been simplified). This construction also tends to be
more robust under changes to the simp lemma set.

* `simpa [rules, ⋯]` will simplify the goal and the type of a
hypothesis `this` if present in the context, then try to close the goal using
the `assumption` tactic.

#TODO: implement `?`

# simpa?!
Defined in: `Std.Tactic.Simpa.tacticSimpa?!_`

This is a "finishing" tactic modification of `simp`. It has two forms.

* `simpa [rules, ⋯] using e` will simplify the goal and the type of
`e` using `rules`, then try to close the goal using `e`.

Simplifying the type of `e` makes it more likely to match the goal
(which has also been simplified). This construction also tends to be
more robust under changes to the simp lemma set.

* `simpa [rules, ⋯]` will simplify the goal and the type of a
hypothesis `this` if present in the context, then try to close the goal using
the `assumption` tactic.

#TODO: implement `?`

# sizeOf_list_dec
Defined in: `List.tacticSizeOf_list_dec`

This tactic, added to the `decreasing_trivial` toolbox, proves that
`sizeOf a < sizeOf as` when `a ∈ as`, which is useful for well founded recursions
over a nested inductive like `inductive T | mk : List T → T`.

# skip
Defined in: `Lean.Parser.Tactic.skip`

`skip` does nothing.

# sleep
Defined in: `Lean.Parser.Tactic.sleep`

The tactic `sleep ms` sleeps for `ms` milliseconds and does nothing.
It is used for debugging purposes only.

# slice_lhs
Defined in: `sliceLHS`

`slice_lhs a b => tac` zooms to the left hand side, uses associativity for categorical
composition as needed, zooms in on the `a`-th through `b`-th morphisms, and invokes `tac`.

# slice_rhs
Defined in: `sliceRHS`

`slice_rhs a b => tac` zooms to the right hand side, uses associativity for categorical
composition as needed, zooms in on the `a`-th through `b`-th morphisms, and invokes `tac`.

# slim_check
Defined in: `slimCheckSyntax`

`slim_check` considers a proof goal and tries to generate examples
that would contradict the statement.

Let's consider the following proof goal.

```lean
xs : List ℕ,
h : ∃ (x : ℕ) (H : x ∈ xs), x < 3
⊢ ∀ (y : ℕ), y ∈ xs → y < 5
```

The local constants will be reverted and an instance will be found for
`Testable (∀ (xs : List ℕ), (∃ x ∈ xs, x < 3) → (∀ y ∈ xs, y < 5))`.
The `Testable` instance is supported by an instance of `Sampleable (List ℕ)`,
`Decidable (x < 3)` and `Decidable (y < 5)`.

Examples will be created in ascending order of size (more or less)

The first counter-examples found will be printed and will result in an error:

```
===================
Found problems!
xs := [1, 28]
x := 1
y := 28
-------------------
```

If `slim_check` successfully tests 100 examples, it acts like
admit. If it gives up or finds a counter-example, it reports an error.

For more information on writing your own `Sampleable` and `Testable`
instances, see `Testing.SlimCheck.Testable`.

Optional arguments given with `slim_check (config : { ... })`
* `numInst` (default 100): number of examples to test properties with
* `maxSize` (default 100): final size argument

Options:
* `set_option trace.slim_check.decoration true`: print the proposition with quantifier annotations
* `set_option trace.slim_check.discarded true`: print the examples discarded because they do not
  satisfy assumptions
* `set_option trace.slim_check.shrink.steps true`: trace the shrinking of counter-example
* `set_option trace.slim_check.shrink.candidates true`: print the lists of candidates considered
  when shrinking each variable
* `set_option trace.slim_check.instance true`: print the instances of `testable` being used to test
  the proposition
* `set_option trace.slim_check.success true`: print the tested samples that satisfy a property

# smul_tac
Defined in: `RatFunc.tacticSmul_tac`

Solve equations for `RatFunc K` by applying `RatFunc.induction_on`.

# solve
Defined in: `solve`

Similar to `first`, but succeeds only if one the given tactics solves the current goal.

# solve_by_elim
Defined in: `Mathlib.Tactic.SolveByElim.solveByElimSyntax`

`solve_by_elim` calls `apply` on the main goal to find an assumption whose head matches
and then repeatedly calls `apply` on the generated subgoals until no subgoals remain,
performing at most `maxDepth` (defaults to 6) recursive steps.

`solve_by_elim` discharges the current goal or fails.

`solve_by_elim` performs backtracking if subgoals can not be solved.

By default, the assumptions passed to `apply` are the local context, `rfl`, `trivial`,
`congrFun` and `congrArg`.

The assumptions can be modified with similar syntax as for `simp`:
* `solve_by_elim [h₁, h₂, ..., hᵣ]` also applies the given expressions.
* `solve_by_elim only [h₁, h₂, ..., hᵣ]` does not include the local context,
  `rfl`, `trivial`, `congrFun`, or `congrArg` unless they are explicitly included.
* `solve_by_elim [-h₁, ... -hₙ]` removes the given local hypotheses.
* `solve_by_elim using [a₁, ...]` uses all lemmas which have been labelled
  with the attributes `aᵢ` (these attributes must be created using `register_label_attr`).

`solve_by_elim*` tries to solve all goals together, using backtracking if a solution for one goal
makes other goals impossible.
(Adding or removing local hypotheses may not be well-behaved when starting with multiple goals.)

Optional arguments passed via a configuration argument as `solve_by_elim (config := { ... })`
- `maxDepth`: number of attempts at discharging generated subgoals
- `symm`: adds all hypotheses derived by `symm` (defaults to `true`).
- `exfalso`: allow calling `exfalso` and trying again if `solve_by_elim` fails
  (defaults to `true`).
- `transparency`: change the transparency mode when calling `apply`. Defaults to `.default`,
  but it is often useful to change to `.reducible`,
  so semireducible definitions will not be unfolded when trying to apply a lemma.

See also the doc-comment for `Mathlib.Tactic.BacktrackConfig` for the options
`proc`, `suspend`, and `discharge` which allow further customization of `solve_by_elim`.
Both `apply_assumption` and `apply_rules` are implemented via these hooks.

# sorry
Defined in: `Lean.Parser.Tactic.tacticSorry`

The `sorry` tactic closes the goal using `sorryAx`. This is intended for stubbing out incomplete
parts of a proof while still having a syntactically correct proof skeleton. Lean will give
a warning whenever a proof uses `sorry`, so you aren't likely to miss it, but
you can double check if a theorem depends on `sorry` by using
`#print axioms my_thm` and looking for `sorryAx` in the axiom list.

# specialize
Defined in: `Lean.Parser.Tactic.specialize`

The tactic `specialize h a₁ ... aₙ` works on local hypothesis `h`.
The premises of this hypothesis, either universal quantifications or
non-dependent implications, are instantiated by concrete terms coming
from arguments `a₁` ... `aₙ`.
The tactic adds a new hypothesis with the same name `h := h a₁ ... aₙ`
and tries to clear the previous one.

# split
Defined in: `Lean.Parser.Tactic.split`

The `split` tactic is useful for breaking nested if-then-else and `match` expressions into separate cases.
For a `match` expression with `n` cases, the `split` tactic generates at most `n` subgoals.

For example, given `n : Nat`, and a target `if n = 0 then Q else R`, `split` will generate
one goal with hypothesis `n = 0` and target `Q`, and a second goal with hypothesis
`¬n = 0` and target `R`.  Note that the introduced hypothesis is unnamed, and is commonly
renamed used the `case` or `next` tactics.

- `split` will split the goal (target).
- `split at h` will split the hypothesis `h`.

# split_ands
Defined in: `Std.Tactic.tacticSplit_ands`

`split_ands` applies `And.intro` until it does not make progress.

# split_ifs
Defined in: `Mathlib.Tactic.splitIfs`

Splits all if-then-else-expressions into multiple goals.
Given a goal of the form `g (if p then x else y)`, `split_ifs` will produce
two goals: `p ⊢ g x` and `¬p ⊢ g y`.
If there are multiple ite-expressions, then `split_ifs` will split them all,
starting with a top-most one whose condition does not contain another
ite-expression.
`split_ifs at *` splits all ite-expressions in all hypotheses as well as the goal.
`split_ifs with h₁ h₂ h₃` overrides the default names for the hypotheses.

# squeeze_scope
Defined in: `Std.Tactic.squeezeScope`

The `squeeze_scope` tactic allows aggregating multiple calls to `simp` coming from the same syntax
but in different branches of execution, such as in `cases x <;> simp`.
The reported `simp` call covers all simp lemmas used by this syntax.
```
@[simp] def bar (z : Nat) := 1 + z
@[simp] def baz (z : Nat) := 1 + z

@[simp] def foo : Nat → Nat → Nat
  | 0, z => bar z
  | _+1, z => baz z

example : foo x y = 1 + y := by
  cases x <;> simp? -- two printouts:
  -- "Try this: simp only [foo, bar]"
  -- "Try this: simp only [foo, baz]"

example : foo x y = 1 + y := by
  squeeze_scope
    cases x <;> simp -- only one printout: "Try this: simp only [foo, baz, bar]"
```

# stop
Defined in: `Lean.Parser.Tactic.tacticStop_`

`stop` is a helper tactic for "discarding" the rest of a proof:
it is defined as `repeat sorry`.
It is useful when working on the middle of a complex proofs,
and less messy than commenting the remainder of the proof.

# subst
Defined in: `Lean.Parser.Tactic.subst`

`subst x...` substitutes each `x` with `e` in the goal if there is a hypothesis
of type `x = e` or `e = x`.
If `x` is itself a hypothesis of type `y = e` or `e = y`, `y` is substituted instead.

# subst_eqs
Defined in: `Std.Tactic.tacticSubst_eqs`

`subst_eqs` applies `subst` to all equalities in the context as long as it makes progress.

# subst_vars
Defined in: `Lean.Parser.Tactic.substVars`

Applies `subst` to all hypotheses of the form `h : x = t` or `h : t = x`.

# substs
Defined in: `Mathlib.Tactic.Substs.substs`

Applies the `subst` tactic to all given hypotheses from left to right.

# success_if_fail_with_msg
Defined in: `Mathlib.Tactic.successIfFailWithMsg`

`success_if_fail_with_msg msg tacs` runs `tacs` and succeeds only if they fail with the message
`msg`.

`msg` can be any term that evaluates to an explicit `String`.

# suffices
Defined in: `Lean.Parser.Tactic.tacticSuffices_`

Given a main goal `ctx ⊢ t`, `suffices h : t' from e` replaces the main goal with `ctx ⊢ t'`,
`e` must have type `t` in the context `ctx, h : t'`.

The variant `suffices h : t' by tac` is a shorthand for `suffices h : t' from by tac`.
If `h :` is omitted, the name `this` is used.

# suffices
Defined in: `Mathlib.Tactic.tacticSuffices_`


# swap
Defined in: `Mathlib.Tactic.tacticSwap`

`swap` is a shortcut for `pick_goal 2`, which interchanges the 1st and 2nd goals.

# swap_var
Defined in: `Mathlib.Tactic.«tacticSwap_var__,,»`

`swap_var swap_rule₁, swap_rule₂, ⋯` applies `swap_rule₁` then `swap_rule₂` then `⋯`.

A *swap_rule* is of the form `x y` or `x ↔ y`, and "applying it" means swapping the variable name
`x` by `y` and vice-versa on all hypotheses and the goal.

```lean
example {P Q : Prop} (q : P) (p : Q) : P ∧ Q := by
  swap_var p ↔ q
  exact ⟨p, q⟩
```

# symm
Defined in: `Mathlib.Tactic.tacticSymm_`

* `symm` applies to a goal whose target has the form `t ~ u` where `~` is a symmetric relation,
  that is, a relation which has a symmetry lemma tagged with the attribute [symm].
  It replaces the target with `u ~ t`.
* `symm at h` will rewrite a hypothesis `h : t ~ u` to `h : u ~ t`.

# symm_saturate
Defined in: `Mathlib.Tactic.tacticSymm_saturate`

For every hypothesis `h : a ~ b` where a `@[symm]` lemma is available,
add a hypothesis `h_symm : b ~ a`.

# tauto
Defined in: `Mathlib.Tactic.Tauto.tauto`

`tauto` breaks down assumptions of the form `_ ∧ _`, `_ ∨ _`, `_ ↔ _` and `∃ _, _`
and splits a goal of the form `_ ∧ _`, `_ ↔ _` or `∃ _, _` until it can be discharged
using `reflexivity` or `solve_by_elim`.
This is a finishing tactic: it either closes the goal or raises an error.

The Lean 3 version of this tactic by default attempted to avoid classical reasoning
where possible. This Lean 4 version makes no such attempt. The `itauto` tactic
is designed for that purpose.

# tfae_finish
Defined in: `Mathlib.Tactic.TFAE.tfaeFinish`

`tfae_finish` is used to close goals of the form `TFAE [P₁, P₂, ...]` once a sufficient collection
of hypotheses of the form `Pᵢ → Pⱼ` or `Pᵢ ↔ Pⱼ` have been introduced to the local context.

`tfae_have` can be used to conveniently introduce these hypotheses; see `tfae_have`.

Example:
```lean
example : TFAE [P, Q, R] := by
  tfae_have 1 → 2
  · /- proof of P → Q -/
  tfae_have 2 → 1
  · /- proof of Q → P -/
  tfae_have 2 ↔ 3
  · /- proof of Q ↔ R -/
  tfae_finish
```

# tfae_have
Defined in: `Mathlib.Tactic.TFAE.tfaeHave`

`tfae_have` introduces hypotheses for proving goals of the form `TFAE [P₁, P₂, ...]`. Specifically,
`tfae_have i arrow j` introduces a hypothesis of type `Pᵢ arrow Pⱼ` to the local context,
where `arrow` can be `→`, `←`, or `↔`. Note that `i` and `j` are natural number indices (beginning
at 1) used to specify the propositions `P₁, P₂, ...` that appear in the `TFAE` goal list. A proof
is required afterward, typically via a tactic block.

```lean
example (h : P → R) : TFAE [P, Q, R] := by
  tfae_have 1 → 3
  · exact h
  ...
```
The resulting context now includes `tfae_1_to_3 : P → R`.

The introduced hypothesis can be given a custom name, in analogy to `have` syntax:
```lean
tfae_have h : 2 ↔ 3
```

Once sufficient hypotheses have been introduced by `tfae_have`, `tfae_finish` can be used to close
the goal.

```lean
example : TFAE [P, Q, R] := by
  tfae_have 1 → 2
  · /- proof of P → Q -/
  tfae_have 2 → 1
  · /- proof of Q → P -/
  tfae_have 2 ↔ 3
  · /- proof of Q ↔ R -/
  tfae_finish
```

# trace
Defined in: `Lean.Parser.Tactic.trace`

Evaluates a term to a string (when possible), and prints it as a trace message.

# trace
Defined in: `Lean.Parser.Tactic.traceMessage`

`trace msg` displays `msg` in the info view.

# trace_state
Defined in: `Lean.Parser.Tactic.traceState`

`trace_state` displays the current state in the info view.

# trans
Defined in: `Mathlib.Tactic.tacticTrans___`

`trans` applies to a goal whose target has the form `t ~ u` where `~` is a transitive relation,
that is, a relation which has a transitivity lemma tagged with the attribute [trans].

* `trans s` replaces the goal with the two subgoals `t ~ s` and `s ~ u`.
* If `s` is omitted, then a metavariable is used instead.

# transitivity
Defined in: `Mathlib.Tactic.tacticTransitivity___`


# triv
Defined in: `Std.Tactic.triv`

Tries to solve the goal using a canonical proof of `True`, or the `rfl` tactic.
Unlike `trivial` or `trivial'`, does not use the `contradiction` tactic.

# trivial
Defined in: `Lean.Parser.Tactic.tacticTrivial`

`trivial` tries different simple tactics (e.g., `rfl`, `contradiction`, ...)
to close the current goal.
You can use the command `macro_rules` to extend the set of tactics used. Example:
```
macro_rules | `(tactic| trivial) => `(tactic| simp)
```

# try
Defined in: `Lean.Parser.Tactic.tacticTry_`

`try tac` runs `tac` and succeeds even if `tac` failed.

# type_check
Defined in: `tacticType_check_`

Type check the given expression, and trace its type.

# unfold
Defined in: `Lean.Parser.Tactic.unfold`

* `unfold id` unfolds definition `id`.
* `unfold id1 id2 ...` is equivalent to `unfold id1; unfold id2; ...`.

For non-recursive definitions, this tactic is identical to `delta`.
For definitions by pattern matching, it uses "equation lemmas" which are
autogenerated for each match arm.

# unfold_let
Defined in: `Mathlib.Tactic.unfoldLetStx`

`unfold_let x y z at loc` unfolds the local definitions `x`, `y`, and `z` at the given
location, which is known as "zeta reduction."
This also exists as a `conv`-mode tactic.

If no local definitions are given, then all local definitions are unfolded.
This variant also exists as the `conv`-mode tactic `zeta`.

This is similar to the `unfold` tactic, which instead is for unfolding global definitions.

# unfold_projs
Defined in: `Mathlib.Tactic.unfoldProjsStx`

`unfold_projs at loc` unfolds projections of class instances at the given location.
This also exists as a `conv`-mode tactic.

# unhygienic
Defined in: `Lean.Parser.Tactic.tacticUnhygienic_`

`unhygienic tacs` runs `tacs` with name hygiene disabled.
This means that tactics that would normally create inaccessible names will instead
make regular variables. **Warning**: Tactics may change their variable naming
strategies at any time, so code that depends on autogenerated names is brittle.
Users should try not to use `unhygienic` if possible.
```
example : ∀ x : Nat, x = x := by unhygienic
  intro            -- x would normally be intro'd as inaccessible
  exact Eq.refl x  -- refer to x
```

# unit_interval
Defined in: `Tactic.Interactive.tacticUnit_interval`

A tactic that solves `0 ≤ ↑x`, `0 ≤ 1 - ↑x`, `↑x ≤ 1`, and `1 - ↑x ≤ 1` for `x : I`.

# unreachable!
Defined in: `Std.Tactic.unreachable`

This tactic causes a panic when run (at compile time).
(This is distinct from `exact unreachable!`, which inserts code which will panic at run time.)

It is intended for tests to assert that a tactic will never be executed, which is otherwise an
unusual thing to do (and the `unreachableTactic` linter will give a warning if you do).

The `unreachableTactic` linter has a special exception for uses of `unreachable!`.
```
example : True := by trivial <;> unreachable!
```

# use
Defined in: `Mathlib.Tactic.useSyntax`

`use e₁, e₂, ⋯` is similar to `exists`, but unlike `exists` it is equivalent to applying the tactic
`refine ⟨e₁, e₂, ⋯, ?_, ⋯, ?_⟩` with any number of placeholders (rather than just one) and
then trying to close goals associated to the placeholders with a configurable discharger (rather
than just `try trivial`).

Examples:

```lean
example : ∃ x : Nat, x = x := by use 42

example : ∃ x : Nat, ∃ y : Nat, x = y := by use 42, 42

example : ∃ x : String × String, x.1 = x.2 := by use ("forty-two", "forty-two")
```

`use! e₁, e₂, ⋯` is similar but it applies constructors everywhere rather than just for
goals that correspond to the last argument of a constructor. This gives the effect that
nested constructors are being flattened out, with the supplied values being used along the
leaves and nodes of the tree of constructors.
With `use!` one can feed in each `42` one at a time:

```lean
example : ∃ p : Nat × Nat, p.1 = p.2 := by use! 42, 42

example : ∃ p : Nat × Nat, p.1 = p.2 := by use! (42, 42)
```

The second line makes use of the fact that `use!` tries refining with the argument before
applying a constructor. Also note that `use`/`use!` by default uses a tactic
called `use_discharger` to discharge goals, so `use! 42` will close the goal in this example since
`use_discharger` applies `rfl`, which as a consequence solves for the other `Nat` metavariable.

These tactics take an optional discharger to handle remaining explicit `Prop` constructor arguments.
By default it is `use (discharger := try with_reducible use_discharger) e₁, e₂, ⋯`.
To turn off the discharger and keep all goals, use `(discharger := skip)`.
To allow "heavy refls", use `(discharger := try use_discharger)`.

# use!
Defined in: `Mathlib.Tactic.«tacticUse!___,,»`

`use e₁, e₂, ⋯` is similar to `exists`, but unlike `exists` it is equivalent to applying the tactic
`refine ⟨e₁, e₂, ⋯, ?_, ⋯, ?_⟩` with any number of placeholders (rather than just one) and
then trying to close goals associated to the placeholders with a configurable discharger (rather
than just `try trivial`).

Examples:

```lean
example : ∃ x : Nat, x = x := by use 42

example : ∃ x : Nat, ∃ y : Nat, x = y := by use 42, 42

example : ∃ x : String × String, x.1 = x.2 := by use ("forty-two", "forty-two")
```

`use! e₁, e₂, ⋯` is similar but it applies constructors everywhere rather than just for
goals that correspond to the last argument of a constructor. This gives the effect that
nested constructors are being flattened out, with the supplied values being used along the
leaves and nodes of the tree of constructors.
With `use!` one can feed in each `42` one at a time:

```lean
example : ∃ p : Nat × Nat, p.1 = p.2 := by use! 42, 42

example : ∃ p : Nat × Nat, p.1 = p.2 := by use! (42, 42)
```

The second line makes use of the fact that `use!` tries refining with the argument before
applying a constructor. Also note that `use`/`use!` by default uses a tactic
called `use_discharger` to discharge goals, so `use! 42` will close the goal in this example since
`use_discharger` applies `rfl`, which as a consequence solves for the other `Nat` metavariable.

These tactics take an optional discharger to handle remaining explicit `Prop` constructor arguments.
By default it is `use (discharger := try with_reducible use_discharger) e₁, e₂, ⋯`.
To turn off the discharger and keep all goals, use `(discharger := skip)`.
To allow "heavy refls", use `(discharger := try use_discharger)`.

# use_discharger
Defined in: `Mathlib.Tactic.tacticUse_discharger`

Default discharger to try to use for the `use` and `use!` tactics.
This is similar to the `trivial` tactic but doesn't do things like `contradiction` or `decide`.

# use_finite_instance
Defined in: `tacticUse_finite_instance`


# whisker_simps
Defined in: `Mathlib.Tactic.BicategoryCoherence.whisker_simps`

Simp lemmas for rewriting a 2-morphism into a normal form.

# whnf
Defined in: `Mathlib.Tactic.tacticWhnf__`

`whnf at loc` puts the given location into weak-head normal form.
This also exists as a `conv`-mode tactic.

Weak-head normal form is when the outer-most expression has been fully reduced, the expression
may contain subexpressions which have not been reduced.

# with_panel_widgets
Defined in: `ProofWidgets.withPanelWidgetsTacticStx`

Display the selected panel widgets in the nested tactic script. For example,
assuming we have written a `GeometryDisplay` component,
```lean
by with_panel_widgets [GeometryDisplay]
  simp
  rfl
```
will show the geometry display alongside the usual tactic state throughout the proof.

# with_reducible
Defined in: `Lean.Parser.Tactic.withReducible`

`with_reducible tacs` excutes `tacs` using the reducible transparency setting.
In this setting only definitions tagged as `[reducible]` are unfolded.

# with_reducible_and_instances
Defined in: `Lean.Parser.Tactic.withReducibleAndInstances`

`with_reducible_and_instances tacs` excutes `tacs` using the `.instances` transparency setting.
In this setting only definitions tagged as `[reducible]` or type class instances are unfolded.

# with_unfolding_all
Defined in: `Lean.Parser.Tactic.withUnfoldingAll`

`with_unfolding_all tacs` excutes `tacs` using the `.all` transparency setting.
In this setting all definitions that are not opaque are unfolded.

# wlog
Defined in: `Mathlib.Tactic.wlog`

`wlog h : P` will add an assumption `h : P` to the main goal, and add a side goal that requires
showing that the case `h : ¬ P` can be reduced to the case where `P` holds (typically by symmetry).

The side goal will be at the top of the stack. In this side goal, there will be two additional
assumptions:
- `h : ¬ P`: the assumption that `P` does not hold
- `this`: which is the statement that in the old context `P` suffices to prove the goal.
  By default, the name `this` is used, but the idiom `with H` can be added to specify the name:
  `wlog h : P with H`.

Typically, it is useful to use the variant `wlog h : P generalizing x y`,
to revert certain parts of the context before creating the new goal.
In this way, the wlog-claim `this` can be applied to `x` and `y` in different orders
(exploiting symmetry, which is the typical use case).

By default, the entire context is reverted.

# zify
Defined in: `Mathlib.Tactic.Zify.zify`

The `zify` tactic is used to shift propositions from `ℕ` to `ℤ`.
This is often useful since `ℤ` has well-behaved subtraction.
```
example (a b c x y z : ℕ) (h : ¬ x*y*z < 0) : c < a + 3*b := by
  zify
  zify at h
  /-
  h : ¬↑x * ↑y * ↑z < 0
  ⊢ ↑c < ↑a + 3 * ↑b
  -/
```
`zify` can be given extra lemmas to use in simplification. This is especially useful in the
presence of nat subtraction: passing `≤` arguments will allow `push_cast` to do more work.
```
example (a b c : ℕ) (h : a - b < c) (hab : b ≤ a) : false := by
  zify [hab] at h
  /- h : ↑a - ↑b < ↑c -/
```
`zify` makes use of the `@[zify_simps]` attribute to move propositions,
and the `push_cast` tactic to simplify the `ℤ`-valued expressions.
`zify` is in some sense dual to the `lift` tactic. `lift (z : ℤ) to ℕ` will change the type of an
integer `z` (in the supertype) to `ℕ` (the subtype), given a proof that `z ≥ 0`;
propositions concerning `z` will still be over `ℤ`. `zify` changes propositions about `ℕ` (the
subtype) to propositions about `ℤ` (the supertype), without changing the type of any variable.

# decide
Defined in: `Lean.Parser.Tactic.decide`

`decide` will attempt to prove a goal of type `p` by synthesizing an instance
of `Decidable p` and then evaluating it to `isTrue ..`. Because this uses kernel
computation to evaluate the term, it may not work in the presence of definitions
by well founded recursion, since this requires reducing proofs.
```
example : 2 + 2 ≠ 5 := by decide
```

# intro match
Defined in: `Lean.Parser.Tactic.introMatch`

The tactic
```
intro
| pat1 => tac1
| pat2 => tac2
```
is the same as:
```
intro x
match x with
| pat1 => tac1
| pat2 => tac2
```
That is, `intro` can be followed by match arms and it introduces the values while
doing a pattern match. This is equivalent to `fun` with match arms in term mode.

# match
Defined in: `Lean.Parser.Tactic.match`
`match` performs case analysis on one or more expressions.
See [Induction and Recursion][tpil4].
The syntax for the `match` tactic is the same as term-mode `match`, except that
the match arms are tactics instead of expressions.
```
example (n : Nat) : n = n := by
  match n with
  | 0 => rfl
  | i+1 => simp
```

[tpil4]: https://leanprover.github.io/theorem_proving_in_lean4/induction_and_recursion.html

# native_decide
Defined in: `Lean.Parser.Tactic.nativeDecide`

`native_decide` will attempt to prove a goal of type `p` by synthesizing an instance
of `Decidable p` and then evaluating it to `isTrue ..`. Unlike `decide`, this
uses `#eval` to evaluate the decidability instance.

This should be used with care because it adds the entire lean compiler to the trusted
part, and the axiom `ofReduceBool` will show up in `#print axioms` for theorems using
this method or anything that transitively depends on them. Nevertheless, because it is
compiled, this can be significantly more efficient than using `decide`, and for very
large computations this is one way to run external programs and trust the result.
```
example : (List.range 1000).length = 1000 := by native_decide
```

# open 
Defined in: `Lean.Parser.Tactic.open`

`open Foo in tacs` (the tactic) acts like `open Foo` at command level,
but it opens a namespace only within the tactics `tacs`.

# set_option
Defined in: `Lean.Parser.Tactic.set_option`

`set_option opt val in tacs` (the tactic) acts like `set_option opt val` at the command level,
but it sets the option only within the tactics `tacs`.

# tac <;> tac'
Defined in: `Lean.Parser.Tactic.«tactic_<;>_»`
`tac <;> tac'` runs `tac` on the main goal and `tac'` on each produced goal,
concatenating all goals produced by `tac'`.

# says
Defined in: `Mathlib.Tactic.Says.says`

# t <;> [t1; t2; ...; tn]
Defined in: `Std.Tactic.seq_focus`

`t <;> [t1; t2; ...; tn]` focuses on the first goal and applies `t`, which should result in `n`
subgoals. It then applies each `ti` to the corresponding goal and collects the resulting
subgoals.

# ·
`· tac` focuses on the main goal and tries to solve it using `tac`, or else fails.

# if h : t then tac1 else tac2
In tactic mode, `if h : t then tac1 else tac2` can be used as alternative syntax for:
```
by_cases h : t
· tac1
· tac2
```
It performs case distinction on `h : t` or `h : ¬t` and `tac1` and `tac2` are the subproofs.

You can use `?_` or `_` for either subproof to delay the goal to after the tactic, but
if a tactic sequence is provided for `tac1` or `tac2` then it will require the goal to be closed
by the end of the block.

# if t then tac1 else tac2
In tactic mode, `if t then tac1 else tac2` is alternative syntax for:
```
by_cases t
· tac1
· tac2
```
It performs case distinction on `h† : t` or `h† : ¬t`, where `h†` is an anonymous
hypothesis, and `tac1` and `tac2` are the subproofs. (It doesn't actually use
nondependent `if`, since this wouldn't add anything to the context and hence would be
useless for proving theorems. To actually insert an `ite` application use
`refine if t then ?_ else ?_`.)  