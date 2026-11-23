import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodTopBot
import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.WeylDualWeylLatticesAgreeOfLowestAlcove
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc

namespace GlobalTheory.Alc

theorem rowE_apply_eq_sum (R : Type) [CommRing R] (r n : ℕ) (a b : Fin r) (f : MvPolynomial (Fin r × Fin n) R) :
    rowE R r n a b f = ∑ s : Fin n, X (a, s) * pderiv (b, s) f := by
  simp [rowE, LinearMap.sum_apply]

theorem weight_rowW_eq_sum {r n : ℕ} (d : Fin r × Fin n →₀ ℕ) (a : Fin r) :
    Finsupp.weight (rowW r n) d a = ∑ s : Fin n, d (a, s) := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp only [Finset.sum_apply, Pi.smul_apply, rowW, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Fintype.sum_prod_type, Finset.sum_eq_single a (fun x _ hx => by simp [Ne.symm hx]) (by simp)]
  simp

theorem weight_rowW_single {r n : ℕ} (v : Fin r × Fin n) :
    Finsupp.weight (rowW r n) (Finsupp.single v 1) = Pi.single v.1 1 := by
  simp [Finsupp.weight_apply, rowW]

theorem X_mul_monomial_pderiv_term {R : Type} [CommRing R] {r n : ℕ} (a b : Fin r) (s : Fin n)
    (d : Fin r × Fin n →₀ ℕ) (c : R) :
    X (a, s) * pderiv (b, s) (monomial d c) =
      monomial (Finsupp.single (a, s) 1 + (d - Finsupp.single (b, s) 1)) (c * (d (b, s) : R)) := by
  rw [pderiv_monomial, X, monomial_mul, one_mul]

end GlobalTheory.Alc

namespace GlobalTheory.Alc

theorem rowE_diag_monomial {R : Type} [CommRing R] {r n : ℕ} (a : Fin r) (μ : Fin r → ℕ)
    (d : Fin r × Fin n →₀ ℕ) (c : R) (hd : Finsupp.weight (rowW r n) d = μ) :
    rowE R r n a a (monomial d c) = (μ a : R) • monomial d c := by
  rw [rowE_apply_eq_sum]
  have hterm : ∀ s : Fin n, X (a, s) * pderiv (a, s) (monomial d c) = monomial d (c * (d (a, s) : R)) := by
    intro s
    rw [X_mul_monomial_pderiv_term]
    by_cases h : d (a, s) = 0
    · simp [h]
    · rw [add_comm, tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr h))]
  simp_rw [hterm]
  rw [← map_sum, ← Finset.mul_sum, smul_monomial, smul_eq_mul, mul_comm]
  congr 2
  rw [← hd, weight_rowW_eq_sum]
  push_cast
  rfl

theorem rowE_monomial_eq_zero {R : Type} [CommRing R] {r n : ℕ} (a b : Fin r) (μ : Fin r → ℕ)
    (d : Fin r × Fin n →₀ ℕ) (c : R) (hd : Finsupp.weight (rowW r n) d = μ) (hb : μ b = 0) :
    rowE R r n a b (monomial d c) = 0 := by
  rw [rowE_apply_eq_sum]
  refine Finset.sum_eq_zero fun s _ => ?_
  have h0 : d (b, s) = 0 := by
    have h1 : ∑ t : Fin n, d (b, t) = 0 := by rw [← weight_rowW_eq_sum, hd, hb]
    exact (Finset.sum_eq_zero_iff.mp h1) s (Finset.mem_univ _)
  rw [X_mul_monomial_pderiv_term, h0]
  simp

theorem rowE_monomial_weight {R : Type} [CommRing R] {r n : ℕ} (a b : Fin r) (μ μ' : Fin r → ℕ)
    (d : Fin r × Fin n →₀ ℕ) (c : R) (hd : Finsupp.weight (rowW r n) d = μ)
    (hμ : μ' + Pi.single b 1 = μ + Pi.single a 1) :
    IsWeightedHomogeneous (rowW r n) (rowE R r n a b (monomial d c)) μ' := by
  rw [rowE_apply_eq_sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun s _ => ?_
  rw [X_mul_monomial_pderiv_term]
  by_cases h : d (b, s) = 0
  · rw [h]; simp only [Nat.cast_zero, mul_zero, map_zero]
    exact isWeightedHomogeneous_zero R _ _
  · refine isWeightedHomogeneous_monomial _ _ _ ?_
    have hle : Finsupp.single (b, s) 1 ≤ d := Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr h)
    have hsplit : Finsupp.weight (rowW r n) (d - Finsupp.single (b, s) 1) + Pi.single b 1 = μ := by
      rw [← weight_rowW_single (b, s), ← map_add, tsub_add_cancel_of_le hle, hd]
    rw [map_add, weight_rowW_single]
    apply add_right_cancel (b := Pi.single b 1)
    rw [hμ, ← hsplit]
    simp only
    abel

theorem rowE_rowWeight : ∀ (R : Type) [CommRing R] (r n : ℕ) (μ : Fin r → ℕ) (f : MvPolynomial (Fin r × Fin n) R),
    IsWeightedHomogeneous (rowW r n) f μ → (∀ a, rowE R r n a a f = (μ a : R) • f) ∧
      ∀ a b, a ≠ b → (μ b = 0 → rowE R r n a b f = 0) ∧
        ∀ μ' : Fin r → ℕ, μ' + Pi.single b 1 = μ + Pi.single a 1 →
          IsWeightedHomogeneous (rowW r n) (rowE R r n a b f) μ' := by
  intro R _ r n μ f hf
  have hmon : ∀ d ∈ f.support, Finsupp.weight (rowW r n) d = μ := fun d hd => hf (mem_support_iff.mp hd)
  refine ⟨fun a => ?_, fun a b _ => ⟨fun hb => ?_, fun μ' hμ => ?_⟩⟩
  · conv_lhs => rw [f.as_sum]
    conv_rhs => rw [f.as_sum]
    rw [map_sum, Finset.smul_sum]
    exact Finset.sum_congr rfl fun d hd => rowE_diag_monomial a μ d _ (hmon d hd)
  · rw [f.as_sum, map_sum]
    exact Finset.sum_eq_zero fun d hd => rowE_monomial_eq_zero a b μ d _ (hmon d hd) hb
  · rw [f.as_sum, map_sum]
    exact IsWeightedHomogeneous.sum _ _ _ fun d hd => rowE_monomial_weight a b μ μ' d _ (hmon d hd) hμ

end GlobalTheory.Alc
