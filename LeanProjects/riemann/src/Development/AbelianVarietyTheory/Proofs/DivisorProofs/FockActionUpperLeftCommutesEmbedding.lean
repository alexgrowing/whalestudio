import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetSNeZero

open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.CharPair

namespace GlobalTheory.CharPair.FirstBlock

section General

variable {K A : Type} [CommRing K] [CommRing A] [Algebra K A]

theorem der_aeval {σ : Type} [Fintype σ] [DecidableEq σ] (d : Derivation K A A) (z : σ → A)
    (G : MvPolynomial σ K) : d (aeval z G) = ∑ i, aeval z (pderiv i G) * d (z i) := by
  induction G using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp [hp, hq, add_mul, Finset.sum_add_distrib]
  | mul_X p n hp =>
    have e : ∀ i, aeval z (pderiv i (p * X n)) * d (z i) =
        (if n = i then aeval z p * d (z i) else 0) + z n * (aeval z (pderiv i p) * d (z i)) := by
      intro i
      by_cases hi : n = i
      · subst hi
        simp [Derivation.leibniz]; ring
      · simp [Derivation.leibniz, hi, pderiv_X, Pi.single_apply]; ring
    simp only [e, Finset.sum_add_distrib]
    simp [hp, Finset.mul_sum]

theorem der_prod {ι : Type} [DecidableEq ι] (d : Derivation K A A) (s : Finset ι) (f : ι → A) :
    d (∏ i ∈ s, f i) = ∑ i ∈ s, (∏ j ∈ s.erase i, f j) * d (f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Derivation.leibniz, ih, Finset.erase_insert ha,
      smul_eq_mul, smul_eq_mul, add_comm, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    have hne : a ≠ i := fun e => ha (e ▸ hi)
    rw [Finset.erase_insert_of_ne hne, Finset.prod_insert (fun h => ha (Finset.mem_of_mem_erase h)),
      mul_assoc]

theorem der_det {n : Type} [Fintype n] [DecidableEq n] (d : Derivation K A A) (M : Matrix n n A) :
    d M.det = ∑ i, (M.updateRow i fun j => d (M i j)).det := by
  simp only [Matrix.det_apply, map_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [← Finset.smul_sum, Units.smul_def, Units.smul_def, map_zsmul, der_prod,
    ← Equiv.sum_comp σ (fun i => ∏ x, (M.updateRow i fun j => d (M i j)) (σ x) x)]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i), Matrix.updateRow_self]
  congr 1
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [Matrix.updateRow_ne (fun e => (Finset.mem_erase.1 hj).1 (σ.injective e))]

end General

variable {P Q R : ℕ}

noncomputable def rowDer (Q R : ℕ) (a a' : Fin P) : Derivation ℂ (Pol P Q R 0) (Pol P Q R 0) :=
  ∑ c : Fin R, (X (Sum.inl a, Sum.inl c) : Pol P Q R 0) • pderiv (Sum.inl a', Sum.inl c)

theorem rowDer_apply (a a' : Fin P) (F : Pol P Q R 0) :
    rowDer Q R a a' F = ∑ c : Fin R, X (Sum.inl a, Sum.inl c) * pderiv (Sum.inl a', Sum.inl c) F := by
  have := map_sum (Derivation.coeFnAddMonoidHom (R := ℂ) (A := Pol P Q R 0) (M := Pol P Q R 0))
    (fun c : Fin R => (X (Sum.inl a, Sum.inl c) : Pol P Q R 0) • pderiv (Sum.inl a', Sum.inl c)) Finset.univ
  have h2 := congrFun this F
  rw [Finset.sum_apply] at h2
  exact h2

theorem rowDer_X_inl_inl (a a' i : Fin P) (c : Fin R) :
    rowDer Q R a a' (X (Sum.inl i, Sum.inl c)) = if i = a' then X (Sum.inl a, Sum.inl c) else 0 := by
  rw [rowDer_apply]
  by_cases h : i = a' <;> simp [pderiv_X, Pi.single_apply, h]

theorem rowDer_w (a a' : Fin P) (b : Fin Q) (c : Fin R) :
    rowDer Q R a a' (X (Sum.inr b, Sum.inl c)) = 0 := by
  rw [rowDer_apply]
  simp [pderiv_X, Pi.single_apply]

theorem rowDer_mR (a a' i : Fin P) (b : Fin Q) :
    rowDer Q R a a' (mR P Q R i b) = if i = a' then mR P Q R a b else 0 := by
  simp only [mR, map_sum, Derivation.leibniz, rowDer_X_inl_inl, rowDer_w, smul_eq_mul]
  split_ifs <;> simp [mul_comm]

theorem rowDer_detR (h : P ≤ R) (a a' : Fin P) :
    rowDer Q R a a' (detR P Q R h) = if a = a' then detR P Q R h else 0 := by
  rw [detR, der_det, Finset.sum_eq_single a']
  · simp only [Matrix.of_apply, rowDer_X_inl_inl, if_true]
    split_ifs with e
    · subst e
      congr 1
      exact Matrix.updateRow_eq_self _ _
    · exact Matrix.det_updateRow_eq_zero (M := Matrix.of fun a c : Fin P =>
        (X (Sum.inl a, Sum.inl (Fin.castLE h c)) : Pol P Q R 0)) e
  · intro i _ hi
    simp only [Matrix.of_apply, rowDer_X_inl_inl, if_neg hi]
    exact Matrix.det_eq_zero_of_row_eq_zero i (by simp)
  · simp

theorem act_eq (a a' : Fin P) (F : Pol P Q R 0) :
    fockAct1 P Q R 0 (Eab (Sum.inl a) (Sum.inl a')) F =
      rowDer Q R a a' F + (if a = a' then (R : ℂ) / 2 else 0) • F := by
  have hpp : ∀ c : Fin R, omE (p := P) (q := Q) (r := R) (s := 0) (Sum.inl a, Sum.inl c) (Sum.inl a', Sum.inl c) F =
      X (Sum.inl a, Sum.inl c) * pderiv (Sum.inl a', Sum.inl c) F + (if a = a' then (1 / 2 : ℂ) else 0) • F := by
    intro c
    simp only [omE, raiB, lowB, linePos]
    by_cases e : a = a' <;> simp [e]
  rw [fockAct1_Eab, LinearMap.sum_apply, Fintype.sum_sum_type, rowDer_apply]
  simp only [hpp, Finset.sum_add_distrib, Finset.univ_eq_empty, Finset.sum_empty, add_zero,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  split_ifs
  · congr 2; ring
  · simp

theorem act_first_block : ∀ (P Q R : ℕ) (h : P ≤ R) (k : ℕ) (a a' : Fin P) (G : Mdl P Q), fockAct1 P Q R 0 (Eab (Sum.inl a) (Sum.inl a')) (embR P Q R h k G) = embR P Q R h k (opR P Q R k (Sum.inl a) (Sum.inl a') G) := by
  intro P Q R h k a a' G
  have hk : rowDer Q R a a' (detR P Q R h ^ k) = (if a = a' then (k : ℂ) else 0) • detR P Q R h ^ k := by
    rw [Derivation.leibniz_pow, rowDer_detR]
    split_ifs
    · rcases k with _ | k
      · simp
      · rw [Nat.cast_smul_eq_nsmul, Nat.add_sub_cancel, smul_eq_mul, ← pow_succ]
    · simp
  have hG : rowDer Q R a a' (aeval (fun ab : Fin P × Fin Q => mR P Q R ab.1 ab.2) G) =
      ∑ b, mR P Q R a b * aeval (fun ab : Fin P × Fin Q => mR P Q R ab.1 ab.2) (pderiv (a', b) G) := by
    rw [der_aeval, Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [rowDer_mR, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [mul_comm]
  have he : ∀ H, embR P Q R h k H =
      aeval (fun ab : Fin P × Fin Q => mR P Q R ab.1 ab.2) H * detR P Q R h ^ k := fun H => rfl
  have ho : opR P Q R k (Sum.inl a) (Sum.inl a') G =
      ∑ b, X (a, b) * pderiv (a', b) G + (if a = a' then (k : ℂ) + (R : ℂ) / 2 else 0) • G := by
    by_cases e : a = a' <;> simp [opR, LinearMap.sum_apply, e]
  rw [act_eq, he, he, ho, Derivation.leibniz, hk, hG, map_add, map_sum, map_smul]
  simp only [map_mul, aeval_X, smul_eq_mul, add_mul, mul_smul_comm, smul_mul_assoc]
  rw [mul_comm (detR P Q R h ^ k)]
  split_ifs
  · module
  · simp

end GlobalTheory.CharPair.FirstBlock
