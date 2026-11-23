import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsMemRowHighestTotalDegreeEqTwo
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CommuteRowOpRightMixedOp
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Sl2NonnegWeightOfHighestWeightVector
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.EqZeroOfPartialSumsNonneg
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RowAddGenericRowAddTerm
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ColumnDegreeLe
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ProdLeadMinorDiagonal

open MvPolynomial Matrix GlobalTheory.Capelli

namespace GlobalTheory.Harm

namespace HighestUnique

variable {K σ : Type*} [Field K]

theorem coeff_X_mul_pderiv (u : σ) (m : σ →₀ ℕ) (P : MvPolynomial σ K) :
    coeff m (X u * pderiv u P) = (m u : K) * coeff m P := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial d r =>
    rw [X_mul_pderiv_monomial, coeff_smul, coeff_monomial]
    split_ifs with h
    · subst h; simp
    · simp
  | add P Q hP hQ => simp only [map_add, mul_add, coeff_add, hP, hQ]

theorem eval_congr_vars {P : MvPolynomial σ K} {x x' : σ → K} (h : ∀ s ∈ P.vars, x s = x' s) :
    eval x P = eval x' P :=
  eval₂Hom_congr' rfl (fun s hs _ => h s hs) rfl

theorem eval_mul_prod_eq {J : Type*} [Fintype J] (B : J → Set σ)
    (hB : ∀ i j, i ≠ j → ∀ s ∈ B i, s ∉ B j) (D : J → MvPolynomial σ K)
    (hD : ∀ j (x x' : σ → K), (∀ s ∈ B j, x s = x' s) → eval x (D j) = eval x' (D j))
    (P : MvPolynomial σ K) (hP : ∀ j, ∃ Q : MvPolynomial σ K, (∀ s ∈ B j, s ∉ Q.vars) ∧ P = Q * D j)
    (hv : ∀ s ∈ P.vars, ∃ j, s ∈ B j) (x₀ x : σ → K) :
    eval x P * ∏ j, eval x₀ (D j) = eval x₀ P * ∏ j, eval x (D j) := by
  classical
  have key : ∀ S : Finset J, eval x P * ∏ j ∈ S, eval x₀ (D j) =
      eval (fun s => if ∃ j ∈ S, s ∈ B j then x₀ s else x s) P * ∏ j ∈ S, eval x (D j) := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | insert j S hj ih =>
      obtain ⟨Q, hQ, e⟩ := hP j
      rw [Finset.prod_insert hj, Finset.prod_insert hj, mul_left_comm, ih]
      set x' : σ → K := fun s => if ∃ j ∈ S, s ∈ B j then x₀ s else x s with hx'
      set x'' : σ → K := fun s => if ∃ i ∈ insert j S, s ∈ B i then x₀ s else x s with hx''
      have h₁ : eval x' (D j) = eval x (D j) := hD j _ _ fun s hs => by
        rw [hx']
        exact if_neg fun ⟨i, hi, hs'⟩ => hB i j (fun e => hj (e ▸ hi)) s hs' hs
      have h₂ : eval x'' (D j) = eval x₀ (D j) := hD j _ _ fun s hs => by
        rw [hx'']
        exact if_pos ⟨j, Finset.mem_insert_self _ _, hs⟩
      have h₃ : eval x'' Q = eval x' Q := eval_congr_vars fun s hs => by
        have : s ∉ B j := fun h => hQ s h hs
        simp [hx', hx'', this]
      rw [e, map_mul, map_mul, h₁, h₂, h₃]
      ring
  rw [key]
  congr 1
  exact eval_congr_vars fun s hs => if_pos (by simpa using hv s hs)

variable [CharZero K] {p q n : ℕ}

theorem weight_of_mem_support (z : Fin p × Fin n → σ) (y : Fin q × Fin n → σ)
    {P : MvPolynomial σ K} {k : Fin n} {w : ℤ} (h : mixedOp K z y k k P = (w : K) • P)
    {m : σ →₀ ℕ} (hm : m ∈ P.support) :
    ∑ a, (m (z (a, k)) : ℤ) - ∑ b, (m (y (b, k)) : ℤ) = w := by
  have := congrArg (coeff m) h
  rw [mixedOp_apply, coeff_sub, coeff_sum, coeff_sum, coeff_smul] at this
  simp only [coeff_X_mul_pderiv, ← Finset.sum_mul, ← sub_mul, smul_eq_mul] at this
  have h2 := mul_right_cancel₀ (mem_support_iff.1 hm) this
  exact_mod_cast h2

omit [CharZero K] in

theorem rowOp_self (z : Fin p × Fin n → σ) {P : MvPolynomial σ K} {a : Fin p} {d : ℕ}
    (h : ∀ m ∈ P.support, ∑ k, m (z (a, k)) = d) : rowOp K z a a P = ((d : ℤ) : K) • P := by
  ext m
  rw [rowOp_apply, coeff_sum, coeff_smul]
  simp only [coeff_X_mul_pderiv, ← Finset.sum_mul, smul_eq_mul]
  by_cases hm : m ∈ P.support
  · rw [← h m hm]; simp
  · rw [notMem_support_iff.1 hm, mul_zero, mul_zero]

theorem casimir_rows [DecidableEq σ] (z : Fin p × Fin n → σ) (hz : Function.Injective z)
    {P : MvPolynomial σ K} (l : Fin p → ℕ) (hrow : ∀ a, ∀ m ∈ P.support, ∑ k, m (z (a, k)) = l a)
    (hinv : ∀ a b : Fin p, a < b → ∀ t : K,
      bind₁ (fun s => X s + ∑ k, if s = z (b, k) then C t * X (z (a, k)) else 0) P = P) :
    ∑ a, ∑ b, rowOp K z a b (rowOp K z b a P) + ((n : K) - (p : K)) • ∑ a, rowOp K z a a P =
      ((∑ i : Fin p, (l i : ℤ) * (l i + p - 1 - 2 * (i : ℕ)) + ((n : ℤ) - p) * ∑ i, (l i : ℤ) : ℤ) : K)
        • P := by
  rw [casimir_on_highest (rowOp K z) (rowOp_lie z hz) P (fun i => l i) ?_
    fun a => rowOp_self z (hrow a)]
  · simp only [fun a => rowOp_self z (hrow a), ← Finset.sum_smul, smul_smul, ← add_smul]
    congr 1
    push_cast
    rfl
  · intro a b hab
    rw [rowOp_apply]
    exact ((rowAdd_invariant_iff (fun k => z (a, k)) (fun k => z (b, k))
      (fun k l e => by simpa using hz e)
      (fun k l e => hab.ne (congrArg Prod.fst (hz e))) P).out 1 2).1 (hinv a b hab)

theorem sum_filter_pad (hp : p ≤ n) (a : Fin p → ℕ) (i : ℕ) :
    ∑ k ∈ Finset.univ.filter (fun k : Fin n => (k : ℕ) < i),
      (if h : (k : ℕ) < p then (a ⟨k, h⟩ : ℤ) else 0) =
      ∑ j ∈ Finset.univ.filter (fun j : Fin p => (j : ℕ) < i), (a j : ℤ) := by
  rw [Finset.sum_filter, Finset.sum_filter, ← sum_dite_lt hp]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> rfl

theorem sum_filter_pad_rev (hq : q ≤ n) (b : Fin q → ℕ) (i : ℕ) :
    ∑ k ∈ Finset.univ.filter (fun k : Fin n => ¬ (k : ℕ) < i),
      (if h : n - 1 - (k : ℕ) < q then (b ⟨n - 1 - k, h⟩ : ℤ) else 0) =
      ∑ j ∈ Finset.univ.filter (fun j : Fin q => (j : ℕ) < n - i), (b j : ℤ) := by
  rw [Finset.sum_filter, Finset.sum_filter, ← sum_dite_rev_lt hq]
  refine Finset.sum_congr rfl fun k _ => ?_
  have := k.2
  dsimp only
  split_ifs <;> first | rfl | omega

section OnePlace

variable [DecidableEq σ] (h : p + q ≤ n) (z : Fin p × Fin n → σ) (hz : Function.Injective z)
  (y : Fin q × Fin n → σ) (hy : Function.Injective y) (hzy : ∀ u w, z u ≠ y w)
  {P : MvPolynomial σ K} (a : Fin p → ℕ) (b : Fin q → ℕ) (ha : Antitone a) (hb : Antitone b)
  (hrz : ∀ i, ∀ m ∈ P.support, ∑ k, m (z (i, k)) = a i)
  (hry : ∀ i, ∀ m ∈ P.support, ∑ k, m (y (i, k)) = b i)
  (hiz : ∀ i j : Fin p, i < j → ∀ t : K,
    bind₁ (fun s => X s + ∑ k, if s = z (j, k) then C t * X (z (i, k)) else 0) P = P)
  (hiy : ∀ i j : Fin q, i < j → ∀ t : K,
    bind₁ (fun s => X s + ∑ k, if s = y (j, k) then C t * X (y (i, k)) else 0) P = P)
  (hharm : ∀ i j, ∑ l, pderiv (z (i, l)) (pderiv (y (j, l)) P) = 0)
  (κ : Fin n → ℤ) (hκ : Antitone κ)
  (hup : ∀ k l, k < l → mixedOp K z y k l P = 0)
  (hwt : ∀ k, mixedOp K z y k k P = (κ k : K) • P)

include h hz hy hzy ha hb hrz hry hiz hiy hharm hκ hup hwt

theorem weight_eq_mixedWeight (hP : P ≠ 0) : κ = mixedWeight n a b := by
  obtain ⟨m, hm⟩ := support_nonempty.2 hP
  have hw := fun k => weight_of_mem_support z y (hwt k) hm
  have hsa : ∑ k, ∑ i, (m (z (i, k)) : ℤ) = ∑ i, (a i : ℤ) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => by exact_mod_cast hrz i m hm
  have hsb : ∑ k, ∑ i, (m (y (i, k)) : ℤ) = ∑ i, (b i : ℤ) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => by exact_mod_cast hry i m hm
  refine casimir_value_strict κ _ hκ (antitone_mixedWeight n ha hb) (fun i => ?_) ?_ (le_of_eq ?_)
  · have h₁ := column_degree_le z hz P a hrz hiz
      (Finset.univ.filter fun k : Fin n => (k : ℕ) < i) m hm
    have h₂ := column_degree_le y hy P b hry hiy
      (Finset.univ.filter fun k : Fin n => ¬ (k : ℕ) < i) m hm
    have c₁ : (Finset.univ.filter fun k : Fin n => (k : ℕ) < i).card = min n i :=
      Fin.card_filter_val_lt
    have c₂ : (Finset.univ.filter fun k : Fin n => ¬ (k : ℕ) < i).card = n - i := by
      have := Finset.card_filter_add_card_filter_not (s := Finset.univ)
        (fun k : Fin n => (k : ℕ) < i)
      rw [c₁, Finset.card_univ, Fintype.card_fin] at this
      omega
    rw [c₁, Finset.filter_congr (q := fun j : Fin p => (j : ℕ) < i)
      (fun j _ => by have := j.2; omega), Finset.sum_comm] at h₁
    rw [c₂, Finset.sum_comm] at h₂
    rw [← Nat.cast_le (α := ℤ)] at h₁ h₂
    simp only [Nat.cast_sum] at h₁ h₂
    rw [← sum_filter_pad (show p ≤ n by omega)] at h₁
    rw [← sum_filter_pad_rev (show q ≤ n by omega)] at h₂
    have e₁ := Finset.sum_filter_add_sum_filter_not Finset.univ (fun k : Fin n => (k : ℕ) < i)
      fun k => ∑ j, (m (y (j, k)) : ℤ)
    have e₂ := Finset.sum_filter_add_sum_filter_not Finset.univ (fun k : Fin n => (k : ℕ) < i)
      fun k => if h : n - 1 - (k : ℕ) < q then (b ⟨n - 1 - k, h⟩ : ℤ) else 0
    rw [sum_dite_rev_lt (show q ≤ n by omega) fun i => (b i : ℤ)] at e₂
    simp only [← hw, mixedWeight_apply, Finset.sum_sub_distrib]
    linarith
  · rw [sum_mixedWeight h, ← hsa, ← hsb, ← Finset.sum_sub_distrib]
    simp only [hw]
  · have c := casimir_mixedOp z hz y hy hzy P
    rw [casimir_on_highest _ (mixedOp_lie z hz y hy hzy) P κ hup hwt,
      casimir_rows z hz a hrz hiz, casimir_rows y hy b hry hiy] at c
    simp only [hharm, mul_zero, Finset.sum_const_zero, smul_zero, sub_zero] at c
    rw [← add_smul, ← Int.cast_add, ← casimir_value_mixedWeight h] at c
    exact (Int.cast_injective (smul_left_injective K hP c)).symm

theorem notMem_vars : (∀ i (k : Fin n), p ≤ k → z (i, k) ∉ P.vars) ∧
    ∀ j (k : Fin n), (k : ℕ) < n - q → y (j, k) ∉ P.vars := by
  by_cases hP : P = 0
  · simp [hP]
  obtain rfl := weight_eq_mixedWeight h z hz y hy hzy a b ha hb hrz hry hiz hiy hharm κ hκ hup hwt hP
  have key : ∀ m ∈ P.support, (∀ i (k : Fin n), p ≤ k → m (z (i, k)) = 0) ∧
      ∀ j (k : Fin n), (k : ℕ) < n - q → m (y (j, k)) = 0 := by
    intro m hm
    have hw := fun k => weight_of_mem_support z y (hwt k) hm
    have hsa : ∑ k, ∑ i, (m (z (i, k)) : ℤ) = ∑ i, (a i : ℤ) := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => by exact_mod_cast hrz i m hm
    have hsb : ∑ k, ∑ i, (m (y (i, k)) : ℤ) = ∑ i, (b i : ℤ) := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => by exact_mod_cast hry i m hm
    constructor
    · have h₁ : ∀ k ∈ (Finset.univ : Finset (Fin n)),
          (if h : (k : ℕ) < p then (a ⟨k, h⟩ : ℤ) else 0) ≤ ∑ i, (m (z (i, k)) : ℤ) := by
        intro k _
        have h₂ := hw k
        have h₃ : 0 ≤ ∑ i, (m (y (i, k)) : ℤ) := by positivity
        have := k.2
        rw [mixedWeight_apply] at h₂
        split_ifs with hk
        · rw [dif_pos hk, dif_neg (by omega)] at h₂
          linarith
        · positivity
      have h₄ := (Finset.sum_eq_sum_iff_of_le h₁).1
        ((sum_dite_lt (by omega) fun i => (a i : ℤ)).trans hsa.symm)
      intro i k hk
      have h₅ := h₄ k (Finset.mem_univ _)
      rw [dif_neg (by omega), eq_comm,
        Finset.sum_eq_zero_iff_of_nonneg fun _ _ => by positivity] at h₅
      exact_mod_cast h₅ i (Finset.mem_univ _)
    · have h₁ : ∀ k ∈ (Finset.univ : Finset (Fin n)),
          (if h : n - 1 - (k : ℕ) < q then (b ⟨n - 1 - k, h⟩ : ℤ) else 0) ≤
            ∑ i, (m (y (i, k)) : ℤ) := by
        intro k _
        have h₂ := hw k
        have h₃ : 0 ≤ ∑ i, (m (z (i, k)) : ℤ) := by positivity
        have := k.2
        rw [mixedWeight_apply] at h₂
        split_ifs with hk
        · rw [dif_pos hk, dif_neg (by omega)] at h₂
          linarith
        · positivity
      have h₄ := (Finset.sum_eq_sum_iff_of_le h₁).1
        ((sum_dite_rev_lt (by omega) fun i => (b i : ℤ)).trans hsb.symm)
      intro i k hk
      have h₅ := h₄ k (Finset.mem_univ _)
      rw [dif_neg (by omega), eq_comm,
        Finset.sum_eq_zero_iff_of_nonneg fun _ _ => by positivity] at h₅
      exact_mod_cast h₅ i (Finset.mem_univ _)
  constructor
  · intro i k hk hv
    obtain ⟨m, hm, hv⟩ := (mem_vars_iff_mem_support _).1 hv
    exact Finsupp.mem_support_iff.1 hv ((key m hm).1 i k hk)
  · intro i k hk hv
    obtain ⟨m, hm, hv⟩ := (mem_vars_iff_mem_support _).1 hv
    exact Finsupp.mem_support_iff.1 hv ((key m hm).2 i k hk)

end OnePlace

theorem exists_eq_mul_prod_minors [DecidableEq σ] (z : Fin p × Fin n → σ)
    (hz : Function.Injective z) (e : Fin p → Fin n) (he : Function.Injective e)
    {P : MvPolynomial σ K} (c : Fin p → ℕ)
    (hrow : ∀ i, ∀ m ∈ P.support, ∑ k, m (z (i, k)) = partOf c i)
    (hinv : ∀ i j : Fin p, i < j → ∀ t : K,
      bind₁ (fun s => X s + ∑ k, if s = z (j, k) then C t * X (z (i, k)) else 0) P = P)
    (hv : ∀ i k, k ∉ Set.range e → z (i, k) ∉ P.vars)
    (hcol : ∀ k l, k < l → colOp K z (e k) (e l) P = 0) :
    ∃ Q : MvPolynomial σ K, (∀ w : Fin p × Fin p, z (w.1, e w.2) ∉ Q.vars) ∧
      P = Q * ∏ i : Fin p, (Matrix.of fun a b : Fin (i.val + 1) =>
        (X (z (lead i a, e (lead i b))) : MvPolynomial σ K)).det ^ c i := by
  refine eq_mul_prod_minors (fun w => z (w.1, e w.2))
    (hz.comp (Function.injective_id.prodMap he)) P c (fun i m hm => ?_) (fun i j hij => ?_)
    fun k l hkl => ?_
  · rw [← partOf, ← hrow i m hm]
    refine Fintype.sum_of_injective e he _ _ (fun k hk => ?_) fun _ => rfl
    by_contra h0
    exact hv i k hk ((mem_vars_iff_mem_support _).2 ⟨m, hm, Finsupp.mem_support_iff.2 h0⟩)
  · have h₁ := ((rowAdd_invariant_iff (fun k => z (i, k)) (fun k => z (j, k))
      (fun k l e => by simpa using hz e)
      (fun k l e => hij.ne (congrArg Prod.fst (hz e))) P).out 1 2).1 (hinv i j hij)
    refine ((rowAdd_invariant_iff (fun k => z (i, e k)) (fun k => z (j, e k))
      (fun k l e => he (by simpa using hz e))
      (fun k l e => hij.ne (congrArg Prod.fst (hz e))) P).out 2 1).1 (Eq.trans ?_ h₁)
    refine Fintype.sum_of_injective e he _ _ (fun k hk => ?_) fun _ => rfl
    rw [pderiv_eq_zero_of_notMem_vars (hv j k hk), mul_zero]
  · exact ((rowAdd_invariant_iff (fun i => z (i, e k)) (fun i => z (i, e l))
      (fun k l e => by simpa using hz e)
      (fun i j e => hkl.ne (he (congrArg Prod.snd (hz e)))) P).out 2 1).1
      ((colOp_apply _ _ _ _).symm.trans (hcol k l hkl))

end HighestUnique

open HighestUnique in

theorem exists_eq_smul_basePoly {K T : Type*} [Field K] [CharZero K] [Fintype T] {p q n : ℕ}
    (h : p + q ≤ n) (c : T → Fin p → ℕ) (c' : T → Fin q → ℕ) {P : Poly K T p q (Fin n)}
    (hP : P ∈ rowHighest K c c') (κ : T → Fin n → ℤ) (hκ : ∀ t, Antitone (κ t))
    (hup : ∀ t (k l : Fin n), k < l →
      ∑ a, X (xVar t a k) * pderiv (xVar t a l) P - ∑ b, X (yVar t b l) * pderiv (yVar t b k) P = 0)
    (hwt : ∀ t (k : Fin n),
      ∑ a, X (xVar t a k) * pderiv (xVar t a k) P - ∑ b, X (yVar t b k) * pderiv (yVar t b k) P =
        (κ t k : K) • P) :
    ∃ r : K, P = r • basePoly K h c c' := by
  classical
  obtain ⟨hh, hrx, hry, hix, hiy⟩ := mem_rowHighest_iff_of_charZero.1 hP
  simp only [rowAddX_eq_bind₁] at hix
  simp only [rowAddY_eq_bind₁] at hiy
  let z : T → Fin p × Fin n → Var T p q (Fin n) := fun t w => xVar t w.1 w.2
  let y : T → Fin q × Fin n → Var T p q (Fin n) := fun t w => yVar t w.1 w.2
  have hz : ∀ t, Function.Injective (z t) := fun t u w e => by simpa [z, Prod.ext_iff] using e
  have hy : ∀ t, Function.Injective (y t) := fun t u w e => by simpa [y, Prod.ext_iff] using e
  have hzy : ∀ t u w, z t u ≠ y t w := fun t u w => by simp [z, y]
  have hv := fun t => notMem_vars h (z t) (hz t) (y t) (hy t) (hzy t) (partOf (c t)) (partOf (c' t))
    (partOf_antitone _) (partOf_antitone _) (hrx t) (hry t) (hix t) (hiy t)
    (fun i j => (laplacian_apply t i j P).symm.trans (hh t i j)) (κ t) (hκ t)
    (fun k l hkl => (mixedOp_apply _ _ _ _ _).trans (hup t k l hkl))
    (fun k => (mixedOp_apply _ _ _ _ _).trans (hwt t k))
  let e : Fin p → Fin n := Fin.castLE (by omega)
  let e' : Fin q → Fin n := fun b => Fin.rev (Fin.castLE (by omega) b)
  have he : ∀ k : Fin n, k ∉ Set.range e → p ≤ k := fun k hk =>
    not_lt.1 fun h' => hk ⟨⟨k, h'⟩, rfl⟩
  have he' : ∀ k : Fin n, k ∉ Set.range e' → (k : ℕ) < n - q := fun k hk =>
    not_le.1 fun h' => hk ⟨⟨n - 1 - k, by have := k.2; omega⟩, by
      ext; have := k.2; simp only [e', Fin.val_rev, Fin.val_castLE]; omega⟩
  have hX := fun t => exists_eq_mul_prod_minors (z t) (hz t) e (Fin.castLE_injective _) (c t)
    (hrx t) (hix t) (fun i k hk => (hv t).1 i k (he k hk)) fun k l hkl => by
      have h₁ := hup t (e k) (e l) hkl
      rw [Finset.sum_eq_zero (f := fun b => X (yVar t b (e l)) * pderiv (yVar t b (e k)) P),
        sub_zero] at h₁
      · exact (colOp_apply _ _ _ _).trans h₁
      · intro b _
        rw [pderiv_eq_zero_of_notMem_vars ((hv t).2 b (e k) ?_), mul_zero]
        have := k.2
        simp only [e, Fin.val_castLE]; omega
  have hY := fun t => exists_eq_mul_prod_minors (y t) (hy t) e'
    (Fin.rev_injective.comp (Fin.castLE_injective _)) (c' t)
    (hry t) (hiy t) (fun i k hk => (hv t).2 i k (he' k hk)) fun k l hkl => by
      have h₁ := hup t (e' l) (e' k) (Fin.rev_lt_rev.2 hkl)
      rw [Finset.sum_eq_zero (f := fun a => X (xVar t a (e' l)) * pderiv (xVar t a (e' k)) P),
        zero_sub, neg_eq_zero] at h₁
      · exact (colOp_apply _ _ _ _).trans h₁
      · intro b _
        rw [pderiv_eq_zero_of_notMem_vars ((hv t).1 b (e' k) ?_), mul_zero]
        have := k.2
        simp only [e', Fin.val_rev, Fin.val_castLE]; omega
  let B : T ⊕ T → Set (Var T p q (Fin n)) := Sum.elim
    (fun t => Set.range fun w : Fin p × Fin p => z t (w.1, e w.2))
    (fun t => Set.range fun w : Fin q × Fin q => y t (w.1, e' w.2))
  let D : T ⊕ T → Poly K T p q (Fin n) := Sum.elim
    (fun t => ∏ i : Fin p, (Matrix.of fun a b : Fin (i.val + 1) =>
      (X (z t (lead i a, e (lead i b))) : Poly K T p q (Fin n))).det ^ c t i)
    (fun t => ∏ i : Fin q, (Matrix.of fun a b : Fin (i.val + 1) =>
      (X (y t (lead i a, e' (lead i b))) : Poly K T p q (Fin n))).det ^ c' t i)
  have hD : ∏ j, D j = basePoly K h c c' := by
    simp only [D, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, basePoly, minorProd, xMinor,
      yMinor, baseCovec, baseVec, xForm_single, yForm_single, ← Finset.prod_mul_distrib]
    rfl
  let x₀ : Var T p q (Fin n) → K := fun v => Sum.elim (baseCovec K h) (baseVec K h) v.2.1 v.2.2
  refine ⟨eval x₀ P, MvPolynomial.funext fun x => ?_⟩
  have key := eval_mul_prod_eq B ?_ D ?_ P ?_ ?_ x₀ x
  · rw [← map_prod, ← map_prod, hD, eval_basePoly, mul_one] at key
    rw [key, smul_eval]
  · rintro (t | t) (t' | t') hne _ ⟨w, rfl⟩ ⟨w', e⟩
    · exact hne (congrArg Sum.inl (congrArg Prod.fst e).symm)
    · simp [z, y] at e
    · simp [z, y] at e
    · exact hne (congrArg Sum.inr (congrArg Prod.fst e).symm)
  · rintro (t | t) x x' hx
    all_goals
      simp only [D, Sum.elim_inl, Sum.elim_inr, map_prod, map_pow, RingHom.map_det]
      refine Finset.prod_congr rfl fun i _ => ?_
      congr 2
      ext a b
      simp only [RingHom.mapMatrix_apply, map_apply, of_apply, eval_X]
      exact hx _ ⟨(lead i a, lead i b), rfl⟩
  · rintro (t | t)
    · obtain ⟨Q, hQ, e⟩ := hX t
      exact ⟨Q, by rintro _ ⟨w, rfl⟩; exact hQ w, e⟩
    · obtain ⟨Q, hQ, e⟩ := hY t
      exact ⟨Q, by rintro _ ⟨w, rfl⟩; exact hQ w, e⟩
  · rintro ⟨t, a | b, k⟩ hs
    · by_cases hk : k ∈ Set.range e
      · obtain ⟨k, rfl⟩ := hk
        exact ⟨Sum.inl t, (a, k), rfl⟩
      · exact absurd hs ((hv t).1 a k (he k hk))
    · by_cases hk : k ∈ Set.range e'
      · obtain ⟨k, rfl⟩ := hk
        exact ⟨Sum.inr t, (b, k), rfl⟩
      · exact absurd hs ((hv t).2 b k (he' k hk))

end GlobalTheory.Harm
