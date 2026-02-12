import Lean.Data.AssocList
import Mathlib.Tactic.Ring

/- README BEFORE STARTING: this file supposes some degree of familiarity with Lean. It does *not* provide any information regarding the system: if you need that, please turn to online sources; see https://leanprover-community.github.io/learn.html for pointers. It defines a set of tactics that emulate the tree-based proof style we discussed in class inside of Lean. You are free to use them or to go your own way (though don't just delegate to automatic tactics, ofc). The exercises are located at the end of this file. -/


/- Reencoding the rules of natural deduction inside of Lean's  -/
/- Impl -/
lemma impl_elim {A B: Prop} : (A → B) → A → B := by lia
/- impl_intro: handled via the intro tactic -/

/- And -/
lemma and_intro      {A B: Prop} : A → B → A ∧ B := by lia
lemma and_elim_left  {A B: Prop} : A ∧ B → A     := by lia
lemma and_elim_right {A B: Prop} : A ∧ B → A     := by lia

/- Or -/
lemma or_intro_left  {A B: Prop} : A → A ∨ B := by lia
lemma or_intro_right {A B: Prop} : B → A ∨ B := by lia
lemma or_elim        {A B C: Prop} : A ∨ B → (A → C) → (B → C) → C := by lia

/- False -/
lemma dne {A : Prop} : ¬¬A → A := by lia
lemma raa {A : Prop} : (¬A → ⊥) → A := by intros h; by_cases A; lia; exfalso; apply h; lia
/- If you think about it hard enough, you can see that dne and raa really are the same (¬X is just
   syntactic sugar for X → ⊥) -/
lemma false_elim {A : Prop} : ⊥ → A := by intros f; simp at f

/- Bi-implication -/
lemma biimpl_intro      {A B: Prop} : (A → B) → (B → A) → (A ↔ B) := by lia
lemma biimpl_elim_left  {A B: Prop} : (A ↔ B) → A → B := by lia
lemma biimpl_elim_right {A B: Prop} : (A ↔ B) → B → A := by lia

/- Not -/
lemma not_intro {A: Prop} : (A → ⊥) → ¬A := by intros h; assumption
lemma not_elim  {A: Prop} : ¬A → A → ⊥   := by lia


/- Custom tactics (introduced through macros) -/
macro "impl_intro" name:ident: tactic => `(tactic| intros $name)
macro "impl_elim": tactic => `(tactic| apply impl_elim)
macro "and_intro": tactic => `(tactic| apply and_intro)
macro "and_elim_left": tactic => `(tactic| apply and_elim_left)
macro "and_elim_right": tactic => `(tactic| apply and_elim_right)
macro "or_elim": tactic => `(tactic| apply or_elim)
macro "or_intro_left": tactic => `(tactic| apply or_intro_left)
macro "or_intro_right": tactic => `(tactic| apply or_intro_right)
macro "dne": tactic => `(tactic| apply dne)
macro "raa": tactic => `(tactic| apply raa)
macro "false_elim": tactic => `(tactic| apply false_elim) /-恒假直接得出想要的-/
macro "biimpl_intro": tactic => `(tactic| apply biimpl_intro)
macro "biimpl_elim_left": tactic => `(tactic| apply biimpl_elim_left)
macro "biimpl_elim_right": tactic => `(tactic| apply biimpl_elim_right)
macro "not_intro": tactic => `(tactic| apply not_intro)
macro "not_elim": tactic => `(tactic| apply not_elim)

macro "from_premise" p:ident: tactic => `(tactic| apply $p)
macro "from_premise_auto": tactic => `(tactic| assumption)


/- Some examples -/
example {A B C: Prop} (P₁: A ∨ (B ∨ C)) (P₂: A → C) (P₃: B → C) : C := by
  or_elim /- Three branches: one per premise for this inference rule -/
  . /- Oh no, metavariables! This is what these variables of the form ?X are. They represent
       expressions whose exact value Lean could not deduce from the context alone. We can resolve
       the ambiguity by providing explicit values via the `change` tactic. -/
    change (A ∨ (B ∨ C)); from_premise P₁
  . impl_intro Pa
    . impl_elim
      . change A → C; from_premise P₂
      . from_premise_auto
  . impl_intro Pbvc
    . or_elim
      . change (B ∨ C); from_premise Pbvc
      . from_premise P₃
      . impl_intro Pc
        . from_premise Pc

example {A B: Prop} (a: A) (b: B) : (A ∧ B) ∧ (B ∧ A) := by
  and_intro
  . and_intro
    . from_premise a
    . from_premise b
  . and_intro
    . from_premise_auto /- Actually, there is no need to refer to the premises' name explicitly -/
    . from_premise_auto


/- Exercises (replace the sorries with actual proofs)
   Typing unicode symbols in Lean (refresher):
   . ∧: \and
   . ∨: \or
   . ⊥: \bot
   . →: \-> or \imp
   . ↔: \iff
   . ¬: \not
   . P₁: P\1

  I did not check every single tactic, any bugs left are yours to fix. -/
section Exercises
  variable (A B C: Prop) /-A B C都为逻辑命题-/

  lemma exercise₁: A → (B → A) := by /-要从A推出B蕴含A-/
    impl_intro hA /-引入A作为假设-/
    impl_intro hB /-B也作为假设-/
    from_premise hA /-已经假设了A，直接拿出来用-/

  lemma exercise₂: ⊥ → A := by /-恒假推出A-/
    false_elim

  lemma exercise₃ (P: A → B) : A → (B ∨ C) := by
    /-前提是A蕴含B，要求推出A蕴含(B或C)-/
    impl_intro hA
    or_intro_left
    impl_elim
    from_premise P /-已知条件直接完成这个目标-/
    from_premise hA /-假设完成这个-/

  lemma exercise₄ (P: ¬C) (Q: (¬B) → C) : B := by
    raa
    impl_intro hNotB
    have hC : C := by /-我声明：我将得到一个名叫 hC 的东西，它的类型是 C，并且我接下来要给出一个证明（by ...）来说明这件事是真的。-/
      from_premise Q
      from_premise hNotB
    from_premise P
    from_premise hC

  lemma exercise₅ (P: A) : ¬((¬A) ∧ B) := by
    not_intro
    impl_intro h
    have hNotA : ¬A := by
      and_elim_left
      from_premise h
    not_elim
    from_premise hNotA
    from_premise P

  lemma exercise₆: (A → (¬A)) → (¬A) := by
    impl_intro hA
    not_intro
    impl_intro a
    have hNotA : ¬A := by /-先构造A否-/
      impl_elim
      from_premise hA
      from_premise a
    from_premise hNotA
    from_premise a

  lemma exercise₇: (A → B) ↔ ((¬B) → (¬A)) := by
    biimpl_intro -- 分两条路证明
    · impl_intro hAB
      impl_intro hNotB
      not_intro
      impl_intro a
      have b : B := by
        exact hAB a -- 类型class完全匹配就直接结束
      not_elim
      · exact hNotB
      · exact b
    · impl_intro hContra
      impl_intro a
      raa
      impl_intro hNotB
      have hNotA : ¬A := by
        exact hContra hNotB
      not_elim
      · exact hNotA
      · exact a
end Exercises
