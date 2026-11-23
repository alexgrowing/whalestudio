import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowForms.Imports
import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem constantCoeff_eq_zero_of_isProjPrime {F : Type*} [Field F] {n : ℕ}
    {P : Ideal (MvPolynomial (Fin n) F)} (hP : IsProjPrime P) {f : MvPolynomial (Fin n) F}
    (hf : f ∈ P) : constantCoeff f = 0 := by
  by_contra h
  have h0 : homogeneousComponent 0 f ∈ P := hP.isHomog f hf 0
  rw [homogeneousComponent_zero] at h0
  apply hP.isPrime.ne_top
  refine Ideal.eq_top_of_isUnit_mem _ h0 ?_
  have hc : coeff 0 f ≠ 0 := by simpa [constantCoeff] using h
  exact hc.isUnit.map C

theorem one_le_of_isProjPrime {F : Type*} [Field F] {n k : ℕ}
    {P : Ideal (MvPolynomial (Fin n) F)} (hP : IsProjPrime P)
    (hk : ringKrullDim (MvPolynomial (Fin n) F ⧸ P) = ((k : ℕ) : WithBot ℕ∞)) : 1 ≤ k := by
  rcases Nat.eq_zero_or_pos k with rfl | h
  · exfalso
    have := hP.isPrime
    have : Ring.KrullDimLE 0 (MvPolynomial (Fin n) F ⧸ P) := by
      rw [ringKrullDimZero_iff_ringKrullDim_eq_zero]
      simpa using hk
    have hmax : P.IsMaximal :=
      Ideal.Quotient.maximal_of_isField _ Ring.KrullDimLE.isField_of_isDomain
    have hle : P ≤ RingHom.ker (constantCoeff : MvPolynomial (Fin n) F →+* F) :=
      fun f hf => constantCoeff_eq_zero_of_isProjPrime hP hf
    have heq := hmax.eq_of_le (RingHom.ker_ne_top _) hle
    obtain ⟨j, hj⟩ := hP.isRelevant
    rw [heq] at hj
    exact hj (by simp [RingHom.mem_ker])
  · exact h

theorem ChowFormExists.proof (h₁ : IncIdealDim.Statement) (h₂ : IncIdealPrime.Statement) :
    ChowFormExists.Statement := by
  intro F _ n k P hP hdim
  have hk : 1 ≤ k := one_le_of_isProjPrime hP hdim
  obtain ⟨j, -⟩ := hP.isRelevant
  have hn : 0 < n := j.pos
  have hQ : (incIdeal P k).IsPrime := h₂ F n k P hP.isPrime hP.isRelevant
  have hdimQ := h₁ F n k (k - 1) P hP (by rw [Nat.sub_add_cancel hk]; exact hdim)
  have hS : ringKrullDim (MvPolynomial (Fin k × Fin n) F) = ((k * n : ℕ) : WithBot ℕ∞) := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field,
      Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, zero_add]
  have hsum := GroundTheory.Arith.Abelian.Jacobian.height_add_ringKrullDim_quotient F (incIdeal P k)
  rw [hdimQ, hS] at hsum
  have hkn : k ≤ k * n := Nat.le_mul_of_pos_right k hn
  obtain ⟨m, hm1, hm2⟩ : ∃ m, k * n - k + min k (k - 1) = m ∧ m + 1 = k * n :=
    ⟨_, rfl, by generalize k * n = N at hkn ⊢; omega⟩
  rw [hm1, ← hm2] at hsum
  have hht : (incIdeal P k).height = 1 := by
    generalize (incIdeal P k).height = h at hsum
    have h' : (h + m : ℕ∞) = ((m + 1 : ℕ) : ℕ∞) := by
      have : ((h + m : ℕ∞) : WithBot ℕ∞) = (((m + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
        push_cast at hsum ⊢
        exact hsum
      exact_mod_cast this
    induction h using ENat.recTopCoe with
    | top => exact (ENat.natCast_ne_top (m + 1) h'.symm).elim
    | coe a =>
      norm_cast at h' ⊢
      omega
  have hne : incIdeal P k ≠ ⊥ := Ideal.ne_bot_of_height_eq_one hht
  obtain ⟨g, hgmem, hgp⟩ := Ideal.IsPrime.exists_mem_prime_of_ne_bot hQ hne
  have hspan := Ideal.eq_span_singleton_of_height_eq_one hht hgmem hgp
  refine ⟨g, hgp.ne_zero, fun f => ?_⟩
  rw [← Ideal.mem_span_singleton, ← hspan]
  simp only [incIdeal, Submodule.mem_iInf, RingHom.mem_ker]

end GroundTheory.Heights₂.Heights
