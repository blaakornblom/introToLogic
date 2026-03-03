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
-- 引入了皮亞諾公理，即：一個自然數要麽是0，要麽是另一個自然數的後繼數。
| Zero
| Succ (n: MyNat)

-- 定義對象
def my_var_zero : MyNat := MyNat.Zero
def my_var_two  : MyNat := MyNat.Succ (MyNat.Succ my_var_zero)

-- 打開「MyNat」這個命名空間
open MyNat -- This just makes it so that we can type Zero instead of MyNat.Zero
def my_var_zero' : MyNat := Zero
-- 定義「my_var_zero'」，其類型是「MyNat」，并且與「MyNat.Zero」等價。
-- 這裡沒有寫 `MyNat`，但 Lean 可以自動推導出來。
-- 語意上等同於：「def my_var_two' : MyNat := Succ (Succ Zero)」
def my_var_two' := Succ (Succ my_var_zero')

@[simp]
-- @[simp]修飾器 (decorator) 讓這個定義可自動展開 目前不用去管説是
-- 定義了 a + b，其是 order-sensitive的，并且類型都是MyNat.
def my_add (a b: MyNat) :=
  match a with
  | .Zero => b
  | .Succ a' =>
    Succ (my_add a' b)
-- 遞歸定義自然數加法. 不理解 内存不會爆炸嗎? 什麽都用遞歸真的很無語

-- #eval 跟證明沒有半點關係，純計算函數。
#eval my_add Zero Zero               -- Expected value: Zero
#eval my_add Zero (Succ Zero)        -- Expected value: Succ Zero
#eval my_add Zero (Succ (Succ Zero)) -- Expected value: Succ (Succ Zero)

deriving instance DecidableEq for MyNat
-- deriving: 編譯器去自動生成一些程式碼。把一個「樣板化、可機械生成」的工作交給 Lean.
-- instance: 這個定義是給編譯器自動使用的，不是給人直接呼叫的
-- DecidableEq for MyNat: 為MyNat派生DecidableEq 的 instance
#test my_add Zero Zero               = MyNat.Zero
#test my_add Zero (Succ Zero)        = Succ Zero
#test my_add Zero (Succ (Succ Zero)) = Succ (Succ Zero)


def my_add_zero_x_is_x: ∀x, my_add Zero x = x -- 定理聲明，其後内容是完成證明之。
:= by -- 進入tactics模式
  intros x -- 引入一個x
  unfold my_add -- 展開my_add, 走 .Zero 分支，讓待證明内容變成 x = x.
  rfl -- 等式的自反性

def my_add_zero_x_is_x' : ∀x, my_add Zero x = x := by
  simp -- 交給simp自動完成證明，不需要手動去展開unfold etc.

#print my_var_zero
#print my_add
#print my_add_zero_x_is_x

def my_add_x_zero_is_x_failed : ∀x, my_add x Zero = x -- What we want to prove
:= by
  intros x
  unfold my_add -- unfold 只能把第一個參數(x)遞歸成其自身，沒有辦法進行更進一步的分析
  match x with -- 對x進行分類討論
  | .Zero => simp -- 如果x是0的話那麽simp就可以自動完成
  | .Succ x' => -- 如果是另一個自然數的後繼數的話那麽
    simp -- simp還是用不了，回到了原待証命題平移后的命題
    sorry -- 直接撂攤子走人 不証了就是説

def my_add_x_zero_is_x : ∀x, my_add x Zero = x := by
  intros x
  induction x with -- 對x進行結構歸納
  | Zero => simp
  | Succ x' ih => -- ih是歸納假設「x' + 0 = x'」
    simp -- 展開my_add, 得到 Succ (my_add x' Zero) = Succ x'
    apply ih -- 目標只剩「my_add x' Zero = x'」，其正好是假設ih。

-- 待證明
def my_add_succ:
  ∀(n m: MyNat), my_add n (Succ m) = Succ (my_add n m)
:= by
  intros n m
  induction n with
  | Zero => simp
  | Succ x' ih =>
    simp
    apply ih


-- 用`rw`重寫證明交換律，并且用到了下面兩個已經證明的定理:
-- `my_add_x_zero_is_x` and `my_add_succ`.
def my_add_comm:
  ∀(n m: MyNat), my_add n m = my_add m n
:= by
  intros n m
  induction n with
  | Zero =>
    simp -- n=0时直接用simp解决
    rw [my_add_x_zero_is_x] --rw是在干嘛，rw是在执行「找到并替换」的操作。
    -- my_add m Zero = m 这个事实，把目标里所有的 my_add m Zero 直接换成 m。
  | Succ n' ih => --ih就是归纳假设 只需证明对Succ n'（即 n'+1）也成立。(strong induction)
    show Succ (my_add n' m) = my_add m (Succ n')
    -- show是在告诉我们， n'+m的后继数等于 m+ (n'的后继数).
    rw [my_add_succ]
    rw [ih]

/- 一些个命题逻辑的数据类型-/
inductive Formula where
| And  (f₁ f₂: Formula)
| Or   (f₁ f₂: Formula)
| Impl (f₁ f₂: Formula)
| Not  (f    : Formula)
| Iff  (f₁ f₂: Formula)
| False
| Var (name: String) --原子命题(?)
open Formula
deriving instance DecidableEq for Formula

@[simp] def Formula₁ : Formula := Not (Not (Not (False)))
-- 定义一个公式为 NOT NOT NOT 假
@[simp] def Formula₂ : Formula :=
  Impl
    (Impl (Var "p₀") False)
    (And
      (Iff (Var "p₀") (Var "p₁"))
      (Var "p₅")
    )
-- 这个其实很好懂
-- (p_0 -> F) -> (p_5 ∧ (p_0 ↔ p_1))
@[simp] def Formula₃ : Formula :=
  Not
    (Impl
      (Not (Var "p₁"))
      (Not (Var "p₁"))
    )
-- 到这里都还能懂
-- 一个字符串到布尔值的映射（关联列表），把命题变元名映射到真/假.
def ValuationT := Lean.AssocList String Bool

@[simp] def empty_valuation   : ValuationT := List.toAssocList' []
-- 空的赋值
@[simp] def sample_valuation₁ : ValuationT := List.toAssocList' [("p₀", true), ("p₁", false)]
-- p_0:=1, p_1:=0.
@[simp] def sample_valuation₂ : ValuationT :=
  List.toAssocList'
    [("p₀", true), ("p₁", false), ("p₂", false), ("p₃", false), ("p₄", false), ("p₅", false)]
-- 依此类推
-- 注意上述evaluation并不唯一，evaluation这个东西想要怎么定义都可以。

-- 这一大坨不知道是什么东西来的，讲师写爱懂不懂不懂也无所谓了
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

-- reduce就是命题逻辑自己的eval
#reduce eval_formula_prop? Formula₁ sample_valuation₁
-- 一些evaluation下该命题是可以为T的。
-- 可以自动联想到SAT/3SAT问题，注意SAT/3SAT问题是第一个被证明NP-COMPLETE的问题。
#reduce eval_formula_prop? Formula₂ empty_valuation -- The valuation is not appropriate → none
-- 空赋值，找不到取值，所以求值失败哒。
#reduce eval_formula_prop? Formula₂ sample_valuation₂
#reduce eval_formula_prop? Formula₃ sample_valuation₂
-- 这些懒得看了，反正知道这里是在干什么。

section Exercise₁
  -- This is the Lean version of an exercise from the first problem set.
  -- We want to show that, for a formula f, the number of subformulas is at most one plus two times
  -- the number of connectives that appear in it.

  @[simp] def count_connectives (f: Formula): Nat :=
    match f with
    | .And f1 f2 => 1 + count_connectives f1 + count_connectives f2
    | .Or  f1 f2 => 1 + count_connectives f1 + count_connectives f2 -- 我笑死，直接复制粘贴
    -- We can use `_` as a placeholder for the name of variables if we don't care about them.
    | .Var  _ => 0 -- _其实很简单，haskell学过，但是这里的.Var(原子公式)不贡献connective的数量，所以为0。
    -- | _ => 0 -- 这里漏写了，需要我们自己去展开
    | .False => 0
    | .Not f2 => 1 + count_connectives f2
    | .Impl f1 f2 => 1 + count_connectives f1 + count_connectives f2
    | .Iff f1 f2 => 1 + count_connectives f1 + count_connectives f2
    -- 这里好多都是映射到一个公式,要是有个switch写法就好了.

  #print List -- we use the `List` type below:
  -- input: Formula
  -- output : [Formula]
  -- 感谢有你haskell
  @[simp] def get_all_subformulas (f: Formula) : List Formula :=
    match f with
    | .And f1 f2 | .Or f1 f2 | .Impl f1 f2 | .Iff f1 f2 =>
      -- 泛匹配感谢有你，要不然我要写这么多行代码我要死掉
      -- ++ 代表了列表的拼接，而区别于数值上的计算
      f::(get_all_subformulas f1 ++ get_all_subformulas f2) -- don't mind the weird notations
    | .False | .Var _ => [f]
    | .Not f2 => f :: get_all_subformulas f2
    -- f :: 是cons操作，python中也有一样的操作，例如:
    -- def Operation:: (a, b: List) => List:
    --     return [a]+b

  #print List.length -- we use this function below
  def at_most_1_plus_two_times_connectives_count_subformulas: -- 这里的def不是定义，而是断言assertion，先断言再给出证明
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
    | And f1 f2 f1h f2h | Or f1 f2 f1h f2h | Impl f1 f2 f1h f2h | Iff f1 f2 f1h f2h => -- `f1h` and `f2h` are our induction hypotheses
      -- 偷懒不犯法，我不想自己写
      simp [Nat.left_distrib, Nat.left_distrib]
      rw [lemma1]
      apply Nat.add_le_add -- We have two branches to handle
      . apply f1h -- The `.` marks the beginning og the branch
      . apply f2h
    | Not f1 f1h =>
      simp -- 简化表达式
      lia -- lia是专门针对整数的线性算术不等式
    | Var _ | False => simp
end Exercise₁

-- Onto predicate logic!
structure PredStructure (A: Type) where
  relations: List ((arity: ℕ) ×' ((l: List A) → (l.length = arity) → Bool))
  -- 关系
  functions: List ((arity: ℕ) ×' ((l: List A) → (l.length = arity) → A))
  -- 函数
  constants: List A
  -- 常量

-- A是论域
inductive PredTerm {A: Type} (PS: PredStructure A) where
-- PredTerm就是"能指代一个对象"的表达式
| FunctionApplication
  (n: ℕ) (x: _) (n_ok: PS.functions[n]? = some x) (args: List A)
  (args_length_ok: args.length = x.1)
  -- `args` should really be of type `List (PredTerm PS)` but this would make things surprisingly
  -- more complex. There is some weird syntax here as well, but the good news is, you don't have to
  -- care.
| Const (n: ℕ) (x: _) (n_ok: PS.functions[n]? = some x) (args: List A)
  (args_length_ok: args.length = x.1) -- there's a bug, that n gets defined in here twice.
| Var (name: String)
open PredTerm

inductive PredFormula {A: Type} (PS: PredStructure A) where
| And    (f₁ f₂: PredFormula PS)
| Or     (f₁ f₂: PredFormula PS)
| Impl   (f₁ f₂: PredFormula PS)
| Not    (f    : PredFormula PS)
| Iff    (f₁ f₂: PredFormula PS)
| False
| Exists (name: String) (f: PredFormula PS) -- 一阶谓词逻辑多出来的
| Forall (name: String) (f: PredFormula PS) -- 一阶谓词逻辑多出来的
| Eq     (t₁ t₂: PredTerm PS) -- 一阶谓词逻辑多出来的
| RelationApplication
  (n: ℕ) (x: _) (n_ok: PS.functions[n]? = some x) (args: List (PredTerm PS))
  (args_length_ok: args.length = x.1) -- 一阶谓词逻辑多出来的
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

  def helper_function (name: String) (f: PredTerm PS) : Bool :=
    match f with
    | .Var _ => true
    | .FunctionApplication _ _ _ _ _ => true
    | .Const _ _ _ _ _ => true

  def all_occurrences_free (name: String) (f: PredFormula PS) : Bool :=
  -- Use Case:
  -- input: all_occurrences_free "x" (Forall "y" (And (Var "x") (Var "y")))
  -- output/return: true
  -- name 就是被查询的变量（只能有一个！！！）
  -- f 被查询的一阶谓词逻辑公式
  -- PS 是 PredStructure A 的实例
  -- 返回的是Boolean value
    match f with
    | .And f1 f2 | .Or f1 f2 | .Impl f1 f2 | .Iff f1 f2 => (all_occurrences_free name f1) && (all_occurrences_free name f2)
    | .Forall s f1 | .Exists s f1 =>
      if s == name
      then false
      else all_occurrences_free name f1
    | .Not f1 => all_occurrences_free name f1
    | .False => true
    -- False is trivially true
    | .Eq zuobian youbian => (helper_function name zuobian) && (helper_function name youbian)
    -- PredTerm 内部的变量出现必然自由, true, 虽然结果总归是true但是检查的过程更接近人类(?)
    | .RelationApplication _ _ _ arg _ => arg.all (helper_function name)
    -- 注意到 arg 的类型是 PredTerm 的列表，所以索性逐一检查一下吧家人们
    -- 说实话很浪费时间，但是过程更接近于死脑筋人类 (?)
    -- arg.all 就是 brute force traversal，很无聊很低质
end Exercise₂ -- 这里应该是 end exercise才对
