import Lean.Data.AssocList
import Mathlib.Tactic.Ring

/- Reminder: this is an interactive file. You should see information relevant to the current
   location of your cursor at all points. To check that everything is in order, move it anywhere in
   the following line. -/
#print "This text should be printed out in the information panel"
/- If that is not the case, follow the instructions in the README.md (if you already did that and it
   still does not work, just send me an email over at matthieub@hi.is). DO NOT go through the
   painful experience of using Lean any other way.

   As you are about to notice, Lean is quite different from the logical system discussed in Van
   Dalen's book. As a first-order approximation, we can view it as a weird programming language (the
   Curry-Howard equivalence we briefly discussed gives grounding to this).

   As in any decent programming language, we can define our own types. The two basic kind of types
   are tuples/structures and inductive types. The former allows us to glue existing types together
   (for instance, we could represent the type of 2D coordinates on the discrete plane as a pair of
   ℤ, also written ℤ × ℤ). The latter provides a way of dealing with alternatives, as illustrated
   below: -/
inductive MyNat where
-- Peano axioms: a natural number is either 0 or the successor of another natural number.
| Zero            -- First alternative: the natural number is zero
| Succ (n: MyNat) -- Second alternative: the natural number is the successor of another one

-- We can then define objects of that type:
def my_var_zero : MyNat := MyNat.Zero
def my_var_two  : MyNat := MyNat.Succ (MyNat.Succ my_var_zero)

open MyNat -- This just makes it so that we can type Zero instead of MyNat.Zero
def my_var_zero' : MyNat := Zero
-- We can omit type annotations quite often (Lean is smart enough to reconstruct them)
def my_var_two' := Succ (Succ my_var_zero')

-- We can define functions acting on objects of this type:
@[simp] -- This makes the definition transparent to some Lean tactics — we'll get there
def my_add (a b: MyNat) :=
  -- a is either Zero or the successor of another MyNat (that we arbitrarily call a'):
  match a with
  | .Zero => b -- If it is zero, we just return `b` (since `0 + b` is `b`)
  | .Succ a' =>
    -- If it is something else, we add one to the result of the simpler addition `a' + b`
    Succ (my_add a' b)
-- This function always terminates. Do you see why? Actually, Lean only ever lets us define
-- terminating functions.

-- Is this function correct? If it is, then we would expect it to have the property that `0 + x` is
-- `x` for any `x`. Let's check some simple examples:
#eval my_add Zero Zero               -- Expected value: Zero
#eval my_add Zero (Succ Zero)        -- Expected value: Succ Zero
#eval my_add Zero (Succ (Succ Zero)) -- Expected value: Succ (Succ Zero)

/- Things seem to be quite alright! Let's make this a bit more rigorous by asking Lean to check our
   assumptions automatically. To do that, we need some (always terminating) function for comparing
   two objects of type `MyNat`. We could build it ourselves but we are lazy — at least, I am. Let's
   ask Lean to build this one automatically (this is possible because this is a function that is
   built in a very predictable way; a few other functions can be derived that way). -/
deriving instance DecidableEq for MyNat -- Building that equality checking function
#test my_add Zero Zero               = MyNat.Zero
#test my_add Zero (Succ Zero)        = Succ Zero
#test my_add Zero (Succ (Succ Zero)) = Succ (Succ Zero)

/- Lean confirms that we know how to read, which is great. Now, with this form of testing, we can
   detect issues, but not their absence: we could not write an exhaustive set of tests that covers
   all natural numbers. Luckily for us, Lean also doubles as a proof assistant. Let's formally
   verify our property: -/
def my_add_zero_x_is_x
: ∀x, my_add Zero x = x -- What we want to prove
:= by -- The by keyword lets us switch to tactics mode
  intros x -- We pull `x` into the valuation (our Γ, so to speak)
  unfold my_add -- This replaces `my_add` with its definition mechanically simplify the expression
  /- `unfold` also simplifies the term to some extent. We can understand what happened here by
      pretending that we are the computer:
     `my_add Zero x = x`
     is equivalent to (the weird syntax is required for introducing a local function object)
     ```
     (fun f : a b =>
       match a with
       | .Zero => b
       | .Succ a' => Succ (f a' b)
     ) Zero x = x
     ```
     is equivalent to (By replacing the first argument by its value)
     ```
     (fun f : b =>
       match Zero with
       | .Zero => b
       | .Succ a' => Succ (f a' b)
     ) x = x
     ```
     is equivalent to (We should take the first branch of this match, right?)
     `(fun f : b => b) x = x`
     is equivalent to (By replacing the remaining argument with the provided value)
     `x = x`
     And this is where unfold stops. -/
  rfl -- `x = x` is obviously true
  -- `rfl` stands for reflexivity: we say that this is true because equality is reflexive.

-- We are done! We could do things more compactly:
def my_add_zero_x_is_x' : ∀x, my_add Zero x = x := by
  simp -- `simp` is like a more powerful `unfold`

-- Curry-Howard magic: proofs are normal objects of Lean, like `my_var_zero` or `my_add`:
#print my_var_zero
#print my_add
#print my_add_zero_x_is_x
/- We could prove things without tactics mode, but then we would have to write such objects by hand.
   Proof mode is just an alternative interface for building Lean objects. It is meant to approximate
   pen-and-paper-style proofs. -/

-- Not all proofs are this easy. Consider the following one:
def my_add_x_zero_is_x_failed : ∀x, my_add x Zero = x -- What we want to prove
:= by
  intros x
  unfold my_add -- This time, `unfold` gets stuck (and so would `simp`).
  -- Look at the above closely. There is no trivial mechanical way of simplifying things further.
  -- We could do case-analysis on the value of `x`.
  match x with
  | .Zero => simp -- We can easily finish this branch
  | .Succ x' =>
    simp -- This does simplify things!
    -- Oh, we are back to square one. We need to use some form of recursion to progress. One way of
    -- solving this is to build a proof by induction.
    sorry -- Let's drop this proof and start it again!

def my_add_x_zero_is_x : ∀x, my_add x Zero = x := by
  intros x
  induction x with -- Note the name of the tactic: this is not just a `match`!
  | Zero => simp
  | Succ x' ih => -- In this branch, we gain an induction hypothesis (that I named `ih`)
    simp
    apply ih -- see the cheat sheet for a description of `apply`; we are done!

/- So how does induction work? Consider how we asked Lean to derive the `DecidableEq` function for
   `MyNat`. This is not the only kind of function that Lean can implement mechanically for types.
   Another example of such a function is the so-called induction principle of a type. Unlike
   `DecidableEq`, this one gets systematically and transparently defined by Lean whenever a new type
   gets introduced. The `induction` tactic use this function to generate one branch per constructor
   of our inductive type. In the case of `MyNat`, there are two of those: `Zero` and `Succ`. `Succ`
   is somewhat special in that it takes an argument that is of type `MyNat` itself. In each branch,
   the induction tactic provides an induction hypothesis per constructor argument that is of the
   same type as the initial object. -/

-- Your turn:
def my_add_succ:
  ∀(n m: MyNat), my_add n (Succ m) = Succ (my_add n m)
:= by
  sorry -- remove this line and write a proof instead!

-- This one is a bit trickier. You will need to use the `rw` tactic (see cheatsheet) with
-- `my_add_x_zero_is_x` and `my_add_succ`.
def my_add_comm:
  ∀(n m: MyNat), my_add n m = my_add m n
:= by
  sorry -- remove this line and write a proof instead!

/- Induction will feature prominently in the rest of this course. Indeed, we can define the syntax
   of propositional or predicate logic via inductive types, and we actually already discussed
   proving metaproperties of these logic by induction in the course. Here is an example encoding of
   propositional logic formulas. -/
inductive Formula where
| And  (f₁ f₂: Formula)
| Or   (f₁ f₂: Formula)
| Impl (f₁ f₂: Formula)
| Not  (f    : Formula)
| Iff  (f₁ f₂: Formula)
| False
| Var (name: String)
open Formula
deriving instance DecidableEq for Formula

-- Here are some concrete examples of formulas:
@[simp] def Formula₁ : Formula := Not (Not (Not (False)))
@[simp] def Formula₂ : Formula :=
  Impl
    (Impl (Var "p₀") False)
    (And
      (Iff (Var "p₀") (Var "p₁"))
      (Var "p₅")
    )
@[simp] def Formula₃ : Formula :=
  Not
    (Impl
      (Not (Var "p₁"))
      (Not (Var "p₁"))
    )

-- And here is how we could define a valuation. Don't get caught up in the details, it is normal if
-- you don't quite understand what is going on in the next line.
def ValuationT := Lean.AssocList String Bool

-- The point is, we can now define valuations!
@[simp] def empty_valuation   : ValuationT := List.toAssocList' []
@[simp] def sample_valuation₁ : ValuationT := List.toAssocList' [("p₀", true), ("p₁", false)]
@[simp] def sample_valuation₂ : ValuationT :=
  List.toAssocList'
    [("p₀", true), ("p₁", false), ("p₂", false), ("p₃", false), ("p₄", false), ("p₅", false)]

-- And below is one way of expressing the semantics of propositional logic formulas. Again, you do
-- not need to understand every single detail to proceed.

-- This is just an auxiliary result that I use to define the semantics — feel free to skip this one.
def ListAssoc_contains_impl_ListAssoc_find_successful:
  ∀{K V: Type} [BEq K] (al: Lean.AssocList K V) (k: K),
  al.contains k = true → ∃v, al.find? k = some v
:= by
  intro K V BEqK al k contains
  induction al with
  | nil => unfold Lean.AssocList.contains at contains; simp at contains
  | cons k' v' tail tail_ih =>
    simp [Lean.AssocList.find?]
    generalize h: (k' == k) = b
    cases b
    . simp; unfold Lean.AssocList.contains at contains; simp at contains
      obtain head_case | tail_case := contains
      . simp [h] at head_case
      . apply tail_ih at tail_case
        obtain ⟨v, hv⟩ := tail_case
        exists v
    . simp

@[simp]
def eval_formula_prop?_aux (f: Formula) (lookup: String → Option Prop): Option Prop :=
  match f with
  | .And f₁ f₂ =>
    let p₁ := eval_formula_prop?_aux f₁ lookup
    let p₂ := eval_formula_prop?_aux f₂ lookup
    match p₁, p₂ with
    | some p₁, some p₂ => some (p₁ ∧ p₂)
    | _, _ => none
  | .Or f₁ f₂ =>
    let p₁ := eval_formula_prop?_aux f₁ lookup
    let p₂ := eval_formula_prop?_aux f₂ lookup
    match p₁, p₂ with
    | some p₁, some p₂ => some (p₁ ∨ p₂)
    | _, _ => none
  | .Impl f₁ f₂ =>
    let p₁ := eval_formula_prop?_aux f₁ lookup
    let p₂ := eval_formula_prop?_aux f₂ lookup
    match p₁, p₂ with
    | some p₁, some p₂ => some (p₁ → p₂)
    | _, _ => none
  | .Not f =>
    let p := eval_formula_prop?_aux f lookup
    match p with
    | some p => some (¬p)
    | _ => none
  | .Iff f₁ f₂ =>
    let p₁ := eval_formula_prop?_aux f₁ lookup
    let p₂ := eval_formula_prop?_aux f₂ lookup
    match p₁, p₂ with
    | some p₁, some p₂ => some (p₁ ↔ p₂)
    | _, _ => none
  | .False => some ⊥
  | .Var name => lookup name

@[simp]
def eval_formula_prop? (f: Formula) (c: ValuationT) : Option Prop :=
  eval_formula_prop?_aux
    f
    (fun name =>
      match Lean.AssocList.find? name c with
      | some true  => some True
      | some false => some ⊥
      | none       => none)

-- This is what the result looks like for some chosen formula/valuation pairs.
#reduce eval_formula_prop? Formula₁ sample_valuation₁
#reduce eval_formula_prop? Formula₂ empty_valuation -- The valuation is not appropriate → none
#reduce eval_formula_prop? Formula₂ sample_valuation₂
#reduce eval_formula_prop? Formula₃ sample_valuation₂

section Exercise₁
  -- This is the Lean version of an exercise from the first problem set.
  -- We want to show that, for a formula f, the number of subformulas is at most one plus two times
  -- the number of connectives that appear in it.

  @[simp] def count_connectives (f: Formula): Nat :=
    match f with
    | .And f1 f2 => 1 + count_connectives f1 + count_connectives f2
    | .Or  f1 f2 => sorry -- TODO complete this line
    -- We can use `_` as a placeholder for the name of variables if we don't care about them.
    | .Var  _ => sorry -- TODO complete this line
    -- We can also use `_` as a placeholder for a constructor. We can read it as "for any other
    -- branch".
    | _ => sorry -- TODO replace this line with all the other required branches

  #print List -- we use the `List` type below:
  @[simp] def get_all_subformulas (f: Formula) : List Formula :=
    match f with
    | .And f1 f2 =>
      -- We return `f` itself (`.And f1 f2`) + the subformulas in both of f1 and f2
      f::(get_all_subformulas f1 ++ get_all_subformulas f2) -- don't mind the weird notations
    | _ => sorry -- TODO complete this function

  #print List.length -- we use this function below
  def at_most_1_plus_two_times_connectives_count_subformulas:
    ∀f, (get_all_subformulas f).length ≤ 2*(count_connectives f) + 1
  := by
    intro f
    have lemma1 : -- Introducing a local result for use within this proof. You may want to reuse it.
      ∀f1 f2,
      2 + 2 * count_connectives f1 + 2 * count_connectives f2 =
      (2 * count_connectives f1 + 1) + (2 * count_connectives f2 + 1)
    := by lia -- end of the proof local result
    -- Let's start the induction proper:
    induction f with
    | And f1 f2 f1h f2h => -- `f1h` and `f2h` are our induction hypotheses
      /- I am using theorems/lemmas from Lean's standard library. I found them using
         https://loogle.lean-lang.org/ -/
      simp [Nat.left_distrib, Nat.left_distrib]
      rw [lemma1]
      apply Nat.add_le_add -- We have two branches to handle
      . apply f1h -- The `.` marks the beginning og the branch
      . apply f2h
    | _ => sorry -- TODO handle the other constructors. Most look very similar to the above.
end Exercise₁

-- Onto predicate logic!
structure PredStructure (A: Type) where
  relations: List ((arity: ℕ) ×' ((l: List A) → (l.length = arity) → Bool))
  functions: List ((arity: ℕ) ×' ((l: List A) → (l.length = arity) → A))
  constants: List A

inductive PredTerm {A: Type} (PS: PredStructure A) where
| FunctionApplication
  (n: ℕ) (x: _) (n_ok: PS.functions[n]? = some x) (args: List A)
  (args_length_ok: args.length = x.1)
  -- `args` should really be of type `List (PredTerm PS)` but this would make things surprisingly
  -- more complex. There is some weird syntax here as well, but the good news is, you don't have to
  -- care.
| Const (n: ℕ)
  (n: ℕ) (x: _) (n_ok: PS.functions[n]? = some x) (args: List A)
  (args_length_ok: args.length = x.1)
| Var (name: String)
open PredTerm

inductive PredFormula {A: Type} (PS: PredStructure A) where
| And    (f₁ f₂: PredFormula PS)
| Or     (f₁ f₂: PredFormula PS)
| Impl   (f₁ f₂: PredFormula PS)
| Not    (f    : PredFormula PS)
| Iff    (f₁ f₂: PredFormula PS)
| False
| Exists (name: String) (f: PredFormula PS)
| Forall (name: String) (f: PredFormula PS)
| Eq     (t₁ t₂: PredTerm PS)
| RelationApplication
  (n: ℕ) (x: _) (n_ok: PS.functions[n]? = some x) (args: List (PredTerm PS))
  (args_length_ok: args.length = x.1)
open PredFormula

section Exercise₂
  -- Define a function called `all_occurrences_free` that returns a value of type `Bool`:
  #print Bool
  #print true
  #print false
  -- It should take two arguments: a variable name (of tye `String`) and a `PredFormula`. Its
  -- behavior should correspond to its name. You don't need to prove anything about this function.
  -- You should use the `==` syntax to compare variable names (hint: you can match on the result of
  -- such equality tests; they return a `Bool`):
  #eval "abc" == "def"
  #eval "abc" == "abc"
section Exercise₂
