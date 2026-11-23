import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetSNeZero
import ReciprocityTheory.SemistableReduction.AlgebraicIndependentOfDerivations

open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.CharPair

noncomputable section

namespace GlobalTheory.CharPair.Down

variable {P Q R : ℕ}

theorem pderiv_pderiv_comm {σ : Type} (i j : σ) (f : MvPolynomial σ ℂ) :
    pderiv i (pderiv j f) = pderiv j (pderiv i f) := by
  classical
  have h0 : ⁅(pderiv i : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ)),
      (pderiv j : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ))⁆ = 0 := by
    apply MvPolynomial.derivation_ext
    intro k
    rw [Derivation.commutator_apply, pderiv_X, pderiv_X]
    simp only [Pi.single_apply]
    split_ifs <;> simp
  have := congrArg (fun D : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ) => D f) h0
  simpa [Derivation.commutator_apply, sub_eq_zero] using this

theorem pderiv_s_mR (a' a : Fin P) (b : Fin Q) (c : Fin R) :
    pderiv (Sum.inl a', Sum.inl c) (mR P Q R a b) =
      if a' = a then X (Sum.inr b, Sum.inl c) else 0 := by
  classical
  simp [mR, map_sum, Derivation.leibniz, pderiv_X, Pi.single_apply]
  rcases eq_or_ne a' a with rfl | ha
  · simp
  · simp [ha, Ne.symm ha]

theorem pderiv_w_mR (b' : Fin Q) (a : Fin P) (b : Fin Q) (c : Fin R) :
    pderiv (Sum.inr b', Sum.inl c) (mR P Q R a b) =
      if b' = b then X (Sum.inl a, Sum.inl c) else 0 := by
  classical
  simp [mR, map_sum, Derivation.leibniz, pderiv_X, Pi.single_apply]
  rcases eq_or_ne b' b with rfl | hb
  · simp
  · simp [hb, Ne.symm hb]

theorem embR_eq (h : P ≤ R) (k : ℕ) (G : Mdl P Q) :
    embR P Q R h k G = aeval (fun ab : Fin P × Fin Q => mR P Q R ab.1 ab.2) G * detR P Q R h ^ k := by
  simp [embR]

theorem derivation_det_eq_zero {σ : Type} {n : ℕ} (d : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ))
    (M : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ)) (hM : ∀ i j, d (M i j) = 0) : d M.det = 0 := by
  have e : M.det = aeval (fun ij : Fin n × Fin n => M ij.1 ij.2)
      (Matrix.det (Matrix.mvPolynomialX (Fin n) (Fin n) ℂ)) := by
    rw [← AlgHom.coe_toRingHom, RingHom.map_det]; congr 1; ext i j; simp [Matrix.mvPolynomialX]
  rw [e, ReciprocityTheory.MultiplicativeHeights.DerivationAlgebraicIndependence.derivation_aeval_eq]
  simp [hM]

def blockR (h : P ≤ R) : Matrix (Fin P) (Fin P) (Pol P Q R 0) :=
  Matrix.of fun a c : Fin P => (X (Sum.inl a, Sum.inl (Fin.castLE h c)) : Pol P Q R 0)

theorem detR_eq (h : P ≤ R) : detR P Q R h = (blockR (Q := Q) h).det := rfl

theorem pderiv_w_detR (h : P ≤ R) (b : Fin Q) (c : Fin R) :
    pderiv (Sum.inr b, Sum.inl c) (detR P Q R h) = 0 := by
  classical
  rw [detR_eq]
  apply derivation_det_eq_zero
  intro i j
  simp [blockR, pderiv_X, Pi.single_apply]

theorem pderiv_s_detR (h : P ≤ R) (a : Fin P) (c : Fin R) :
    pderiv (Sum.inl a, Sum.inl c) (detR P Q R h) =
      ∑ j : Fin P, if Fin.castLE h j = c then (blockR (Q := Q) h).adjugate j a else 0 := by
  classical
  rw [detR_eq, Matrix.det_eq_sum_mul_adjugate_row _ a, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hadj : pderiv (Sum.inl a, Sum.inl c) ((blockR (Q := Q) h).adjugate j a) = 0 := by
    rw [Matrix.adjugate_apply]
    apply derivation_det_eq_zero
    intro i j'
    rw [Matrix.updateRow_apply]
    split_ifs with hi
    · simp [Pi.single_apply]; split_ifs <;> simp
    · simp [blockR, pderiv_X, Pi.single_apply, hi]
  rw [Derivation.leibniz, hadj]
  simp [blockR, pderiv_X, Pi.single_apply, eq_comm]
  done

theorem sum_s_pderiv_detR (h : P ≤ R) (a' a : Fin P) :
    ∑ c : Fin R, X (Sum.inl a', Sum.inl c) * pderiv (Sum.inl a, Sum.inl c) (detR P Q R h) =
      if a' = a then detR P Q R h else 0 := by
  classical
  have e : ∀ c : Fin R, X (Sum.inl a', Sum.inl c) * pderiv (Sum.inl a, Sum.inl c) (detR P Q R h) =
      ∑ j : Fin P, if Fin.castLE h j = c then blockR (Q := Q) h a' j * (blockR (Q := Q) h).adjugate j a
        else 0 := by
    intro c
    rw [pderiv_s_detR, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs with hj
    · simp [blockR, hj]
    · simp
  rw [Finset.sum_congr rfl fun c _ => e c, Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [← Matrix.mul_apply, Matrix.mul_adjugate, detR_eq]
  simp [Matrix.one_apply]

abbrev phiR (P Q R : ℕ) : Mdl P Q →ₐ[ℂ] Pol P Q R 0 := aeval fun ab : Fin P × Fin Q => mR P Q R ab.1 ab.2

theorem pderiv_s_phiR (a : Fin P) (c : Fin R) (H : Mdl P Q) :
    pderiv (Sum.inl a, Sum.inl c) (phiR P Q R H) =
      ∑ b' : Fin Q, phiR P Q R (pderiv (a, b') H) * X (Sum.inr b', Sum.inl c) := by
  classical
  rw [ReciprocityTheory.MultiplicativeHeights.DerivationAlgebraicIndependence.derivation_aeval_eq, Fintype.sum_prod_type]
  simp only [pderiv_s_mR, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  simp [Finset.sum_ite_eq]

theorem pderiv_w_phiR (b : Fin Q) (c : Fin R) (H : Mdl P Q) :
    pderiv (Sum.inr b, Sum.inl c) (phiR P Q R H) =
      ∑ a' : Fin P, phiR P Q R (pderiv (a', b) H) * X (Sum.inl a', Sum.inl c) := by
  classical
  rw [ReciprocityTheory.MultiplicativeHeights.DerivationAlgebraicIndependence.derivation_aeval_eq, Fintype.sum_prod_type]
  simp only [pderiv_w_mR, mul_ite, mul_zero]
  simp [Finset.sum_ite_eq]

theorem pderiv_w_detR_pow (h : P ≤ R) (k : ℕ) (b : Fin Q) (c : Fin R) :
    pderiv (Sum.inr b, Sum.inl c) (detR P Q R h ^ k) = 0 := by
  rw [Derivation.leibniz_pow, pderiv_w_detR]; simp

theorem pderiv_w_s_detR_pow (h : P ≤ R) (k : ℕ) (a : Fin P) (b : Fin Q) (c : Fin R) :
    pderiv (Sum.inr b, Sum.inl c) (pderiv (Sum.inl a, Sum.inl c) (detR P Q R h ^ k)) = 0 := by
  rw [pderiv_pderiv_comm, pderiv_w_detR_pow]; simp

theorem sum_s_pderiv_detR_pow (h : P ≤ R) (k : ℕ) (a' a : Fin P) :
    ∑ c : Fin R, X (Sum.inl a', Sum.inl c) * pderiv (Sum.inl a, Sum.inl c) (detR P Q R h ^ k) =
      if a' = a then (k : Pol P Q R 0) * detR P Q R h ^ k else 0 := by
  classical
  simp only [Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul]
  have e : ∀ c : Fin R, X (Sum.inl a', Sum.inl c) *
      ((k : Pol P Q R 0) * (detR P Q R h ^ (k - 1) * pderiv (Sum.inl a, Sum.inl c) (detR P Q R h))) =
      (k : Pol P Q R 0) * detR P Q R h ^ (k - 1) *
        (X (Sum.inl a', Sum.inl c) * pderiv (Sum.inl a, Sum.inl c) (detR P Q R h)) := fun c => by ring
  rw [Finset.sum_congr rfl fun c _ => e c, ← Finset.mul_sum, sum_s_pderiv_detR]
  split_ifs
  · rcases k with _ | k
    · simp
    · simp [pow_succ]; ring
  · simp

theorem omE_down (a : Fin P) (b : Fin Q) (c : Fin R) (f : Pol P Q R 0) :
    omE ((Sum.inr b, Sum.inl c) : Ln P Q R 0) (Sum.inl a, Sum.inl c) f =
      -(pderiv (Sum.inr b, Sum.inl c) (pderiv (Sum.inl a, Sum.inl c) f)) := by
  simp [omE, raiB, lowB, linePos]

theorem partial_derivative_weight_space_formula (h : P ≤ R) (k : ℕ) (a : Fin P) (b : Fin Q) (c : Fin R) (G : Mdl P Q) :
    pderiv (Sum.inr b, Sum.inl c) (pderiv (Sum.inl a, Sum.inl c) (phiR P Q R G * detR P Q R h ^ k)) =
      (∑ b' : Fin Q, (∑ a' : Fin P, phiR P Q R (pderiv (a', b) (pderiv (a, b') G)) *
          X (Sum.inl a', Sum.inl c)) * X (Sum.inr b', Sum.inl c)) * detR P Q R h ^ k
        + phiR P Q R (pderiv (a, b) G) * detR P Q R h ^ k
        + ∑ a' : Fin P, phiR P Q R (pderiv (a', b) G) *
          (X (Sum.inl a', Sum.inl c) * pderiv (Sum.inl a, Sum.inl c) (detR P Q R h ^ k)) := by
  classical
  have hw : pderiv (Sum.inr b, Sum.inl c) (∑ b' : Fin Q, phiR P Q R (pderiv (a, b') G) *
      X (Sum.inr b', Sum.inl c)) = (∑ b' : Fin Q, (∑ a' : Fin P, phiR P Q R (pderiv (a', b) (pderiv (a, b') G)) *
          X (Sum.inl a', Sum.inl c)) * X (Sum.inr b', Sum.inl c)) + phiR P Q R (pderiv (a, b) G) := by
    simp only [map_sum, Derivation.leibniz, pderiv_w_phiR, pderiv_X, smul_eq_mul, Finset.sum_add_distrib]
    rw [add_comm]
    congr 1
    · exact Finset.sum_congr rfl fun b' _ => by ring
    · simp only [Pi.single_apply, Prod.mk.injEq, Sum.inr.injEq, and_true, mul_ite, mul_one, mul_zero]
      simp
  rw [Derivation.leibniz, map_add, smul_eq_mul, smul_eq_mul, Derivation.leibniz, Derivation.leibniz,
    pderiv_s_phiR, hw, pderiv_w_phiR, pderiv_w_s_detR_pow, pderiv_w_detR_pow]
  simp only [smul_eq_mul, mul_zero, add_zero]
  rw [Finset.mul_sum, Finset.sum_congr rfl fun a' _ => (by ring :
    pderiv (Sum.inl a, Sum.inl c) (detR P Q R h ^ k) * (phiR P Q R (pderiv (a', b) G) * X (Sum.inl a', Sum.inl c)) =
      phiR P Q R (pderiv (a', b) G) * (X (Sum.inl a', Sum.inl c) * pderiv (Sum.inl a, Sum.inl c) (detR P Q R h ^ k)))]
  ring

theorem opR_down (k : ℕ) (a : Fin P) (b : Fin Q) (G : Mdl P Q) :
    opR P Q R k (Sum.inr b) (Sum.inl a) G =
      -(∑ a' : Fin P, ∑ b' : Fin Q, X (a', b') * pderiv (a', b) (pderiv (a, b') G)
        + ((R + k : ℕ) : ℂ) • pderiv (a, b) G) := by
  simp [opR, LinearMap.sum_apply, Module.End.mul_apply]

theorem sum_A (h : P ≤ R) (k : ℕ) (a : Fin P) (b : Fin Q) (G : Mdl P Q) :
    ∑ c : Fin R, (∑ b' : Fin Q, (∑ a' : Fin P, phiR P Q R (pderiv (a', b) (pderiv (a, b') G)) *
          X (Sum.inl a', Sum.inl c)) * X (Sum.inr b', Sum.inl c)) * detR P Q R h ^ k =
      (∑ a' : Fin P, ∑ b' : Fin Q, mR P Q R a' b' * phiR P Q R (pderiv (a', b) (pderiv (a, b') G))) *
        detR P Q R h ^ k := by
  rw [← Finset.sum_mul]
  congr 1
  simp only [mR, Finset.sum_mul]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext b'; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a' _ => Finset.sum_congr rfl fun b' _ => Finset.sum_congr rfl fun c _ => ?_
  ring

theorem sum_C (h : P ≤ R) (k : ℕ) (a : Fin P) (b : Fin Q) (G : Mdl P Q) :
    ∑ c : Fin R, ∑ a' : Fin P, phiR P Q R (pderiv (a', b) G) *
        (X (Sum.inl a', Sum.inl c) * pderiv (Sum.inl a, Sum.inl c) (detR P Q R h ^ k)) =
      phiR P Q R (pderiv (a, b) G) * ((k : Pol P Q R 0) * detR P Q R h ^ k) := by
  classical
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, sum_s_pderiv_detR_pow, mul_ite, mul_zero]
  simp

theorem embR_eq' (h : P ≤ R) (k : ℕ) (G : Mdl P Q) :
    embR P Q R h k G = phiR P Q R G * detR P Q R h ^ k := embR_eq h k G

end GlobalTheory.CharPair.Down

namespace GlobalTheory.CharPair

open GlobalTheory.CharPair.Down in

theorem fockAct1_embR_inr_inl (P Q R : ℕ) (h : P ≤ R) (k : ℕ) (a : Fin P) (b : Fin Q) (G : Mdl P Q) :
    fockAct1 P Q R 0 (Eab (Sum.inr b) (Sum.inl a)) (embR P Q R h k G) =
      embR P Q R h k (opR P Q R k (Sum.inr b) (Sum.inl a) G) := by
  rw [fockAct1_Eab, LinearMap.sum_apply, Fintype.sum_sum_type]
  simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero]
  rw [embR_eq', embR_eq', opR_down]
  simp only [omE_down, partial_derivative_weight_space_formula, Finset.sum_neg_distrib, Finset.sum_add_distrib, sum_A, sum_C,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  simp only [map_neg, map_add, map_sum, map_mul, map_smul, phiR, aeval_X]
  rw [nsmul_eq_mul, Algebra.smul_def, map_natCast]
  push_cast
  ring

end GlobalTheory.CharPair
