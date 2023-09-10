import Mathlib.Topology.MetricSpace.CauSeqFilter

namespace Tutorial

noncomputable
section

/- # 実数 
mathlibでは実数型`ℝ`が定義されている。標準的な解析学の教科書と同様に、`ℝ`の項（つまり実数）は
Cauchy列の同値類として定義される。
-/

-- 実数`1`は定数Cauchy列`1,1,1,1,...`から定まる同値類と等しい
example : (1 : ℝ) = Real.ofCauchy (Quotient.mk CauSeq.equiv (CauSeq.const abs 1)) := 
  Real.ofCauchy_one.symm

-- `0.9999999...`をCauchy列として定義する
def «0.9999999» : CauSeq ℚ abs where
  val n := 1 - (10 ^ n : ℚ)⁻¹
  property := by
    intro ε ε0
    suffices ∃ i, ∀ (j : ℕ), j ≥ i → |((10 ^ i : ℚ)⁻¹ - (10 ^ j : ℚ)⁻¹)| < ε by simpa
    have h : ∃ i : ℕ, (ε / 2)⁻¹ < 10 ^ i := pow_unbounded_of_one_lt (ε / 2)⁻¹ (by linarith)
    rcases h with ⟨i, hi⟩
    have hi : 2 * (10 ^ i : ℚ)⁻¹ < ε := (lt_div_iff' (by linarith)).mp (inv_lt_of_inv_lt (half_pos ε0) hi)
    exists i
    intro j hj
    calc |(10 ^ i : ℚ)⁻¹ - (10 ^ j : ℚ)⁻¹|
      _ ≤ |(10 ^ i : ℚ)⁻¹| + |(10 ^ j : ℚ)⁻¹| := by apply abs_sub
      _ ≤ |(10 ^ i : ℚ)⁻¹| + |(10 ^ i : ℚ)⁻¹| := by simpa [abs] using inv_pow_le_inv_pow_of_le (by linarith) hj
      _ = 2 * (10 ^ i : ℚ)⁻¹                  := by simp [abs]; ring
      _ < ε                                   := hi

-- `0.9999999...`は`1`と等しい
theorem «0.9999999 = 1» : Real.ofCauchy (Quotient.mk CauSeq.equiv «0.9999999») = (1 : ℝ) := by
  calc Real.ofCauchy (Quotient.mk CauSeq.equiv «0.9999999»)
    _ = Real.ofCauchy (Quotient.mk CauSeq.equiv (CauSeq.const abs 1)) := ?eq
    _ = (1 : ℝ) := Real.ofCauchy_one
  case eq =>
    rw [«0.9999999»]
    congr 1
    apply Quotient.sound
    intro ε ε0
    suffices ∃ i, ∀ (j : ℕ), j ≥ i → (10 ^ j : ℚ)⁻¹ < ε by simpa [abs]
    -- ヒント: `pow_unbounded_of_one_lt`と`inv_lt_of_inv_lt`を使って、欲しい`i`を手に入れよう
    have h : ∃ i : ℕ, ε⁻¹ < 10 ^ i := pow_unbounded_of_one_lt ε⁻¹ (by linarith)
    rcases h with ⟨i, hi⟩
    have hi : (10 ^ i : ℚ)⁻¹ < ε := inv_lt_of_inv_lt ε0 hi
    exists i
    intro j hj
    calc (10 ^ j : ℚ)⁻¹
      _ ≤ (10 ^ i : ℚ)⁻¹ := inv_pow_le_inv_pow_of_le (by linarith) hj
      _ < ε              := hi

open Filter Topology Set Classical

/-
TIPS: 閉区間`{ x | a ≤ x ∧ x ≤ b }`は`Icc a b`と表す。Inteval-close-closeの略と覚えると良い。
（閉区間は数学の本では`[a, b]`と書かれることが多いが、Leanではこの記号はリストを表す）
-/

/-
このファイルでは実数の重要な性質のひとつである、閉区間`Icc 0 1`のコンパクト性を証明に挑戦しよう。
具体的には、閉区間`Icc 0 1`の任意の開被覆`U : ι → Set ℝ`が有限部分被覆を持つことを背理法を用いて示す。
ここでは区間縮小法を直接用いて証明をする。

1. 閉区間`I(0) := Icc 0 1`から始まる縮小閉区間列 `I(0) ⊇ I(1) ⊇ ...`であって、任意の
  `n`で`I(n)`が有限部分被覆を持たないものを定める。
2. `I(n)`の中間点からなる数列はCauchy列であり、ある実数`c`に収束する。
3. `c`はある開集合`U i`に含まれるが、`n`を十分大きくとれば`I(n) ⊆ U i`とできる。これは`I(n)`が
  有限部分被覆を持たないことに矛盾する。

以下ではステップ1,2の証明があらかじめ与えられており、最後にステップ3が演習問題として残されている。
すぐに問題に取り組みたい人はファイルの最後までスキップしても問題ないだろう。
-/

/- 解答者注: `ι`は添字集合のことだと思われる。 -/

/-- `ℝ`の部分集合`s`の開被覆`U`が有限部分被覆を持つことを表すための命題 -/
def HasFinSubCover {ι : Type} (U : ι → Set ℝ) (s : Set ℝ) : Prop := 
  ∃ (t : Finset ι), s ⊆ ⋃ i ∈ t, U i

variable {ι : Type} (U : ι → Set ℝ)

/-- 区間縮小法の帰納ステップ。区間を二等分して、有限被覆を持たない方を次の区間に選ぶ。-/
def nestedIntervalSucc (a b : ℝ) : ℝ × ℝ :=
  if ¬HasFinSubCover U (Icc a ((a + b) / 2)) then ⟨a, (a + b) / 2⟩ else ⟨(a + b) / 2, b⟩

/-- 区間縮小法 -/
def nestedInterval : ℕ → ℝ × ℝ 
  | 0 => ⟨0, 1⟩
  | n + 1 => nestedIntervalSucc U (nestedInterval n).1 (nestedInterval n).2

/-
以下の記号を導入する。
- `I(n)`: 縮小閉区間列`I(0) ⊇ I(1) ⊇ ...`
- `α n`: `I(n)`の左端
- `β n`: `I(n)`の右端
-/
local notation "α" n:1000 => Prod.fst (nestedInterval U n)
local notation "β" n:1000 => Prod.snd (nestedInterval U n)
local notation "I(" n ")" => Icc (α n) (β n) 

-- 縮小区間列`I(n)`の中間点からなる数列
def nestedIntervalSeq : ℕ → ℝ := fun n ↦ (α n + β n) / 2

variable {U}

lemma hasFinSubCover_concat (hac : HasFinSubCover U (Icc a c)) (hcb : HasFinSubCover U (Icc c b)) :
    HasFinSubCover U (Icc a b) := by
  rcases hac with ⟨ι_ac, cover_ac⟩
  rcases hcb with ⟨ι_cb, cover_cb⟩
  exists ι_ac ∪ ι_cb
  intro x hx
  suffices ∃ i, (i ∈ ι_ac ∨ i ∈ ι_cb) ∧ x ∈ U i by
    simpa using this
  cases le_total x c
  case inl hxc =>
    obtain ⟨i, hi⟩ : ∃ i, i ∈ ι_ac ∧ x ∈ U i := by simpa using cover_ac ⟨hx.left, hxc⟩
    exact ⟨i, Or.inl hi.1, hi.2⟩
  case inr hxc =>
    obtain ⟨i, hi⟩ : ∃ i, i ∈ ι_cb ∧ x ∈ U i := by simpa using cover_cb ⟨hxc, hx.right⟩
    exact ⟨i, Or.inr hi.1, hi.2⟩

lemma not_HasFinSubCover_concat :
    ¬HasFinSubCover U (Icc a b) → HasFinSubCover U (Icc a c) → ¬HasFinSubCover U (Icc c b) := by
  contrapose!
  apply (fun H ↦ hasFinSubCover_concat H.1 H.2)

lemma nestedIntervalSucc_left (h : ¬HasFinSubCover U (Icc a ((a + b) / 2))) : 
    nestedIntervalSucc U a b = ⟨a, (a + b) / 2⟩ := 
  if_pos h
  
lemma nestedIntervalSucc_right (h : HasFinSubCover U (Icc a ((a + b) / 2))) : 
    nestedIntervalSucc U a b = ⟨(a + b) / 2, b⟩ := 
  if_neg (not_not_intro h)

variable (U)

theorem nestedIntervalSucc_eq_or_eq (a b : ℝ) : 
    nestedIntervalSucc U a b = ⟨a, (a + b) / 2⟩ ∨ 
      nestedIntervalSucc U a b = ⟨(a + b) / 2, b⟩ := by
  apply ite_eq_or_eq

theorem nestedInterval_le : ∀ n, α n < β n
  | 0 => Real.zero_lt_one
  | n + 1 => by
    have := nestedInterval_le n
    cases nestedIntervalSucc_eq_or_eq U (α n) (β n) with
    | inl h => rw [nestedInterval, h]; dsimp only; linarith
    | inr h => rw [nestedInterval, h]; dsimp only; linarith

theorem nestedIntervalSeq_is_nested_succ (n : ℕ) : I(n + 1) ⊆ I(n) := by
  have := nestedInterval_le U n
  cases nestedIntervalSucc_eq_or_eq U (α n) (β n) with 
  | inl h => 
    apply Icc_subset_Icc (by rw [nestedInterval, h]) (by rw [nestedInterval, h]; dsimp only; linarith)
  | inr h => 
    apply Icc_subset_Icc (by rw [nestedInterval, h]; dsimp only; linarith) (by rw [nestedInterval, h])

theorem nestedIntervalSeq_is_nested {i j : ℕ} (hij : i ≤ j) : I(j) ⊆ I(i) := by 
  rw [(Nat.add_sub_of_le hij).symm]
  set k := j - i
  induction k with
  | zero => apply rfl.subset
  | succ k ih => intro x hx; apply ih (nestedIntervalSeq_is_nested_succ U (i + k) hx)

theorem nestedIntervalSeq_mem (n : ℕ) : nestedIntervalSeq U n ∈ I(n) := by
  simp only [mem_Icc, nestedIntervalSeq] 
  have := nestedInterval_le U n
  split_ands <;> linarith

theorem nestedIntervalSeq_mem_of_le {i j : ℕ} (hij : i ≤ j): 
    nestedIntervalSeq U j ∈ I(i) := 
  nestedIntervalSeq_is_nested _ hij (nestedIntervalSeq_mem _ _)

variable {U}
  
/-- `I(0)`が有限部分被覆を持たないならば`I(n)`も有限部分被覆を持たない -/
theorem nestedInterval_not_HasFinSubCover (h : ¬HasFinSubCover U I(0)) : ∀ n : ℕ, ¬HasFinSubCover U I(n)
  | 0 => h
  | n + 1 => by
    by_cases H : HasFinSubCover U (Icc (α n) ((α n + β n) / 2))
    case pos =>
      rw [nestedInterval, nestedIntervalSucc_right H]
      apply not_HasFinSubCover_concat ?_ H
      apply nestedInterval_not_HasFinSubCover h n
    case neg =>
      rw [nestedInterval, nestedIntervalSucc_left H]
      apply H

variable (U)

/-- `I(n)`の長さは`(2 ^ n)⁻¹`である -/
theorem nestedInterval_len : ∀ n : ℕ, β n - α n = (2 ^ n : ℝ)⁻¹
  | 0 => by simp [nestedInterval]
  | n + 1 => by
    have ih := nestedInterval_len n
    rcases nestedIntervalSucc_eq_or_eq U (α n) (β n) with H | H <;> 
      rw [nestedInterval, H] <;> field_simp at ih ⊢ <;>
        calc _ = (β n - α n) * 2 ^ n * 2 := by ring
             _ = 2                       := by rw [ih]; ring

theorem nestedIntervalSeq_isCauSeq_aux {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) : 
    |y - x| ≤ (b - a) := by 
  dsimp [Icc] at hx hy
  apply (abs_sub_le_iff.2 ⟨_, _⟩) <;> linarith

theorem nestedIntervalSeq_isCauSeq_aux' {i j : ℕ} (hij : i ≤ j) : 
    |nestedIntervalSeq U j - nestedIntervalSeq U i| ≤ (2 ^ i : ℝ)⁻¹ := by
  have := nestedIntervalSeq_isCauSeq_aux (nestedIntervalSeq_mem U i) (nestedIntervalSeq_mem_of_le U hij)
  simpa [nestedInterval_len] using this

theorem nestedIntervalSeq_isCauSeq : IsCauSeq abs (nestedIntervalSeq U) := by
  intro ε ε0
  have ⟨i, hi⟩ : ∃ i : ℕ, ε⁻¹ < 2 ^ i := pow_unbounded_of_one_lt ε⁻¹ (by linarith)
  have hi : (2 ^ i : ℝ)⁻¹ < ε := inv_lt_of_inv_lt ε0 hi
  exists i
  intro j hj
  calc |nestedIntervalSeq U j - nestedIntervalSeq U i| 
    _ ≤ (2 ^ i : ℝ)⁻¹ := nestedIntervalSeq_isCauSeq_aux' U hj
    _ < ε             := hi

/-- 区間`I(n)`の中間点からなるCauchy列 -/
def nestedIntervalCauSeq : CauSeq ℝ abs where
  val := nestedIntervalSeq U
  property := nestedIntervalSeq_isCauSeq U

-- おまじない。Leanに`ℝ`が完備であることを思い出させています。
local instance : CauSeq.IsComplete ℝ norm := inferInstanceAs (CauSeq.IsComplete ℝ abs)

lemma nestedIntervalSeq_tendsto : 
    Tendsto (nestedIntervalSeq U) atTop (𝓝 (nestedIntervalCauSeq U).lim) := by
  apply (nestedIntervalCauSeq U).tendsto_limit

/-- 区間`I(n)`の中間点からなるCauchy列の極限は`I(n)`に属する -/
lemma nestedIntervalLim_mem (n : ℕ) : (nestedIntervalCauSeq U).lim ∈ I(n) := 
  isClosed_Icc.mem_of_tendsto (nestedIntervalSeq_tendsto U) <|
    eventually_atTop.mpr ⟨n, fun _ ↦ nestedIntervalSeq_mem_of_le U⟩

/-
以上でステップ1,2の証明が与えられている。
以下の補題が役に立つだろう（カーソルを乗せると説明が表示される）
-/
#check nestedInterval_not_HasFinSubCover
#check nestedInterval_len U
#check nestedIntervalLim_mem U

/-
TIPS: 一元集合は`{i}`と表す。証明のどこかで用いるかもしれない。
-/ 

/-- 閉区間`Icc 0 1`はコンパクト -/
theorem HasFinSubCover_of_Icc (hU : ∀ (i : ι), IsOpen (U i)) (cover : Icc 0 1 ⊆ ⋃ (i : ι), U i) : 
    HasFinSubCover U (Icc 0 1) := by 
  by_contra H
  set c := (nestedIntervalCauSeq U).lim
  rcases cover (nestedIntervalLim_mem U 0) with ⟨_, ⟨i, rfl⟩, hU' : c ∈ U i⟩
  rcases Metric.isOpen_iff.mp (hU i) c hU' with ⟨ε, ε0, hε⟩
  have ⟨n, hn⟩ : ∃ n : ℕ, (ε / 2)⁻¹ < 2 ^ n := by
    exact pow_unbounded_of_one_lt (ε / 2)⁻¹ (by linarith)
  suffices HasFinSubCover U I(n) by 
    apply nestedInterval_not_HasFinSubCover H n
    exact this
  suffices I(n) ⊆ U i by
    rw [HasFinSubCover]
    exists {i}
    simp only [Finset.mem_singleton, iUnion_iUnion_eq_left]
    exact this
  suffices ∀ x, x ∈ I(n) → |x - c| < ε by
    intro x hx₁
    exact hε (this x hx₁)
  intro x hx₁
  have hc : c ∈ I(n) := nestedIntervalLim_mem U n
  rw [Icc, mem_setOf_eq] at hx₁ hc
  have aux : |x - c| ≤ β n - α n := by
    rw [abs_sub_le_iff]
    constructor
    · apply sub_le_sub
      · exact hx₁.right
      · exact hc.left
    · apply sub_le_sub
      · exact hc.right
      · exact hx₁.left
  calc |x - c|
    _ ≤ β n - α n          := aux
    _ = (2 ^ n : ℝ)⁻¹      := nestedInterval_len U n
    _ < 2 * (2 ^ n : ℝ)⁻¹  := lt_two_mul_self (by positivity)
    _ < ε                  := (lt_div_iff' (by linarith)).mp (inv_lt_of_inv_lt (half_pos ε0) hn)

-- 空でない上に有界な実数集合が上限を持つことを用いた別証明
/-- 閉区間`Icc 0 1`はコンパクト -/
example (hU : ∀ (i : ι), IsOpen (U i)) (cover : Icc 0 1 ⊆ ⋃ (i : ι), U i) : 
    HasFinSubCover U (Icc 0 1) := by 
  set A := { x : ℝ | x ∈ Icc 0 1 ∧ HasFinSubCover U (Icc 0 x) }
  have A0 : 0 ∈ A := by
    rcases cover (left_mem_Icc.mpr zero_le_one) with ⟨_, ⟨i, rfl⟩, hU' : 0 ∈ U i⟩
    rw [mem_setOf_eq]
    constructor
    · rw [mem_Icc]
      constructor
      · linarith
      · linarith
    · rw [Icc_self, HasFinSubCover]
      exists {i}
      simp only [Finset.mem_singleton, iUnion_iUnion_eq_left, singleton_subset_iff]
      exact hU'
  have A1 : A.Nonempty := ⟨0, A0⟩
  have A2 : 1 ∈ upperBounds A := fun x hx ↦ hx.1.2
  -- `c`は`A`の最小上界
  have ⟨c, ⟨hAc, hAc'⟩⟩ : ∃ c, IsLUB A c := ⟨sSup A, isLUB_csSup A1 ⟨1, A2⟩⟩
  have hc : c ∈ Icc 0 1 := by
    rw [mem_Icc]
    rw [lowerBounds, upperBounds, mem_setOf_eq] at hAc'
    have h₁ : 1 ∈ {x | ∀ ⦃a : ℝ⦄, a ∈ A → a ≤ x} → c ≤ 1 := @hAc' (1 : ℝ)
    rw [mem_setOf_eq] at h₁
    have h₂ : ∀ ⦃a : ℝ⦄, a ∈ A → a ≤ 1 := by
      intro a ha
      rw [mem_setOf_eq, Icc] at ha
      have ha := ha.left
      rw [mem_setOf_eq] at ha
      exact ha.right
    rw [upperBounds, mem_setOf_eq] at hAc
    constructor
    · exact @hAc 0 A0
    · exact h₁ h₂
  rcases cover hc with ⟨_, ⟨i, rfl⟩, hUc' : c ∈ U i⟩
  have hcA : c ∈ A := by
    rcases hc.1.eq_or_lt with rfl | hlt
    · assumption
    · exists hc
      rcases (mem_nhdsWithin_Iic_iff_exists_Ioc_subset' hlt).mp 
        (mem_nhdsWithin_of_mem_nhds <| (hU i).mem_nhds hUc') with ⟨x, hxc, hxU⟩
      rcases ((IsLUB.frequently_mem ⟨hAc, hAc'⟩ A1).and_eventually 
        (Ioc_mem_nhdsWithin_Iic ⟨hxc, le_rfl⟩)).exists with ⟨y, ⟨-, hyf⟩, hy⟩
      apply hasFinSubCover_concat hyf
      exists {i}
      simp only [Finset.mem_singleton, iUnion_iUnion_eq_left]
      have h₁ : Icc y c ⊆ Ioc x c := by
        rw [Icc, Ioc, setOf_subset_setOf]
        intro a ha
        constructor
        · apply lt_of_lt_of_le hy.left
          exact ha.left
        · exact ha.right
      calc Icc y c
        _ ⊆ Ioc x c := h₁
        _ ⊆ U i := hxU
  suffices c = 1 from this.symm ▸ hcA.2
  by_contra hnc
  have hlt : c < 1 := Ne.lt_of_le hnc (A2 hcA)
  rcases (mem_nhdsWithin_Ici_iff_exists_mem_Ioc_Ico_subset hlt).mp
    (mem_nhdsWithin_of_mem_nhds <| (hU i).mem_nhds hUc') with ⟨c', ⟨hc'1, hc'2⟩, hc'U⟩
  have hc'A : c' ∈ A := by
    constructor
    · rw [Icc, mem_setOf_eq]
      constructor
      · have h₁ : 0 ≤ c := @hAc 0 A0
        have h₂ : 0 < c' := calc 0
          _ ≤ c := h₁
          _ < c' := hc'1
        exact le_of_lt h₂
      · exact hc'2
    · apply hasFinSubCover_concat hcA.2
      dsimp [Icc] at hc
      have : c' ∈ Icc 0 1 := ⟨by linarith, by linarith⟩
      rcases cover this with ⟨_, ⟨i', rfl⟩, hUc' : c' ∈ U i'⟩
      -- ヒント: `Ico_union_right`と`union_subset_union`を用いるとよいかもしれない
      rw [HasFinSubCover]
      exists {i, i'}
      rw [←Ico_union_right]
      simp only [Finset.mem_singleton, Finset.mem_insert, iUnion_iUnion_eq_or_left, iUnion_iUnion_eq_left]
      apply union_subset_union
      · exact hc'U
      · rw [singleton_subset_iff]
        exact hUc'
      · exact le_of_lt hc'1
  have h₁ : c' ≤ c := hAc hc'A
  have h₂ : c < c := calc c
    _ < c' := hc'1
    _ ≤ c  := h₁
  apply (lt_self_iff_false c).mp
  exact h₂

end

end Tutorial