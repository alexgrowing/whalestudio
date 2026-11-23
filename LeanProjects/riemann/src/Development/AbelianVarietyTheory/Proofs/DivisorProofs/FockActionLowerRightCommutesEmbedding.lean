import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetSNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockFirstActionMatrixUnitEq

open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.CharPair

noncomputable section

namespace GlobalTheory.CharPair

variable {P Q R : ℕ}

theorem pderiv_detR_wLetter (h : P ≤ R) (b : Fin Q) (c : Fin R) :
    pderiv (Sum.inr b, Sum.inl c) (detR P Q R h) = 0 := by
  let g : Fin P × Fin P → Ix P Q × Ix R 0 := fun ac => (Sum.inl ac.1, Sum.inl (Fin.castLE h ac.2))
  have : detR P Q R h = rename g (Matrix.det (Matrix.mvPolynomialX (Fin P) (Fin P) ℂ)) := by
    rw [detR, ← AlgHom.coe_toRingHom, RingHom.map_det]; congr 1; ext a c; simp [g, Matrix.mvPolynomialX]
  rw [this]
  apply pderiv_eq_zero_of_notMem_vars
  intro hv
  obtain ⟨x, -, hx⟩ := Finset.mem_image.1 (vars_rename g _ hv)
  simp [g] at hx

theorem wPolarize_aeval_mR (b b' : Fin Q) (G : Mdl P Q) :
    ∑ c : Fin R, X (Sum.inr b', Sum.inl c) * pderiv (Sum.inr b, Sum.inl c)
        (aeval (fun ab : Fin P × Fin Q => mR P Q R ab.1 ab.2) G) =
      aeval (fun ab : Fin P × Fin Q => mR P Q R ab.1 ab.2) (∑ a, X (a, b') * pderiv (a, b) G) := by
  induction G using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp only [map_add, mul_add, Finset.sum_add_distrib, hp, hq]
  | mul_X p n hp =>
    have key : ∑ c : Fin R, X (Sum.inr b', Sum.inl c) * pderiv (Sum.inr b, Sum.inl c) (mR P Q R n.1 n.2)
        = aeval (fun ab : Fin P × Fin Q => mR P Q R ab.1 ab.2)
            (∑ a, X (a, b') * pderiv (a, b) (X n : Mdl P Q)) := by
      obtain ⟨a, b''⟩ := n
      by_cases hb : b'' = b
      · subst hb
        simp [mR, pderiv_X, Pi.single_apply, mul_comm]
      · simp [mR, pderiv_X, Pi.single_apply, hb]
    have e1 : ∀ (A B : Pol P Q R 0), ∑ c : Fin R, X (Sum.inr b', Sum.inl c) * pderiv (Sum.inr b, Sum.inl c) (A * B) =
        (∑ c : Fin R, X (Sum.inr b', Sum.inl c) * pderiv (Sum.inr b, Sum.inl c) A) * B +
          A * ∑ c : Fin R, X (Sum.inr b', Sum.inl c) * pderiv (Sum.inr b, Sum.inl c) B := by
      intro A B
      simp only [pderiv_mul, mul_add, Finset.sum_add_distrib]
      rw [Finset.sum_mul, Finset.mul_sum]
      exact congrArg₂ (· + ·) (Finset.sum_congr rfl fun _ _ => (mul_assoc _ _ _).symm)
        (Finset.sum_congr rfl fun _ _ => mul_left_comm _ _ _)
    have e2 : ∀ (A B : Mdl P Q), ∑ a, X (a, b') * pderiv (a, b) (A * B) =
        (∑ a, X (a, b') * pderiv (a, b) A) * B + A * ∑ a, X (a, b') * pderiv (a, b) B := by
      intro A B
      simp only [pderiv_mul, mul_add, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
      congr 1 <;> refine Finset.sum_congr rfl fun _ _ => by ring
    rw [map_mul, aeval_X, e1, hp, key, e2, map_add, map_mul, map_mul, aeval_X]

theorem fockAct1_inr_inr_embR : ∀ (P Q R : ℕ) (h : P ≤ R) (k : ℕ) (b b' : Fin Q) (G : Mdl P Q),
    fockAct1 P Q R 0 (Eab (Sum.inr b) (Sum.inr b')) (embR P Q R h k G) =
      embR P Q R h k (opR P Q R k (Sum.inr b) (Sum.inr b') G) := by
  intro P Q R h k b b' G
  have hD : ∀ c : Fin R, pderiv (Sum.inr b, Sum.inl c) (detR P Q R h ^ k) = 0 := fun c => by
    simp [Derivation.leibniz_pow, pderiv_detR_wLetter]
  have hw := wPolarize_aeval_mR (R := R) b b' G
  rw [fockAct1_Eab, LinearMap.sum_apply, Fintype.sum_sum_type]
  simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero,
    GlobalTheory.CompactHarm.omE_nn (Sum.inr b, Sum.inl _) (Sum.inr b', Sum.inl _) rfl rfl]
  simp only [embR, opR, LinearMap.comp_apply, LinearMap.mulRight_apply, AlgHom.toLinearMap_apply, pderiv_mul, hD,
    mul_zero, add_zero, LinearMap.sub_apply, LinearMap.neg_apply, LinearMap.sum_apply, Module.End.mul_apply,
    LinearMap.smul_apply, Module.End.one_apply, map_sub, map_neg, map_smul, Prod.mk.injEq, Sum.inr.injEq, and_true]
  have e : ∀ x : Fin P, (mulM x b') ((derM x b) G) = X (x, b') * pderiv (x, b) G := fun _ => rfl
  simp only [e, ← hw, Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, Finset.sum_mul, mul_assoc]
  rw [sub_right_inj]
  split_ifs
  · rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
    congr 1
    ring
  · simp

end GlobalTheory.CharPair
