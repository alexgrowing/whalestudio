import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowForms.Imports
import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem IsChowForm.incIdeal_eq_span {F : Type*} [Field F] {n k : ℕ}
    {P : Ideal (MvPolynomial (Fin n) F)} {f : MvPolynomial (Fin k × Fin n) F}
    (hf : IsChowForm P k f) : incIdeal P k = Ideal.span {f} := by
  ext g
  rw [Ideal.mem_span_singleton, ← hf.2 g]
  simp only [incIdeal, Ideal.mem_iInf, RingHom.mem_ker]

theorem constantCoeff_eq_zero_of_isHomogIdeal {F : Type*} [Field F] {n : ℕ}
    {P : Ideal (MvPolynomial (Fin n) F)} (hP : IsHomogIdeal P) (htop : P ≠ ⊤)
    {g : MvPolynomial (Fin n) F} (hg : g ∈ P) : constantCoeff g = 0 := by
  by_contra h
  have h0 := hP g hg 0
  rw [homogeneousComponent_zero, ← constantCoeff_eq] at h0
  exact htop (Ideal.eq_top_of_isUnit_mem _ h0 ((Ne.isUnit h).map C))

theorem IsProjPrime.not_isField_quotient {F : Type*} [Field F] {n : ℕ}
    {P : Ideal (MvPolynomial (Fin n) F)} (hP : IsProjPrime P) :
    ¬ IsField (MvPolynomial (Fin n) F ⧸ P) := by
  intro hfield
  obtain ⟨j, hj⟩ := hP.isRelevant
  have hx : Ideal.Quotient.mk P (X j) ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  obtain ⟨y, hy⟩ := hfield.mul_inv_cancel hx
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [← map_mul, ← map_one (Ideal.Quotient.mk P), Ideal.Quotient.eq] at hy
  have := constantCoeff_eq_zero_of_isHomogIdeal hP.isHomog hP.isPrime.ne_top hy
  simp at this

theorem ConeDimOfChowForm.proof (h₁ : IncIdealDim.Statement) (h₂ : IncIdealPrime.Statement) :
    ConeDimOfChowForm.Statement := by
  intro F _ n k P f hP hf
  have hspan := hf.incIdeal_eq_span
  have hprime : (Ideal.span {f}).IsPrime := hspan ▸ h₂ F n k P hP.isPrime hP.isRelevant
  have hnu : ¬ IsUnit f := fun hu => hprime.ne_top (Ideal.span_singleton_eq_top.mpr hu)
  have hht : (Ideal.span {f}).height = 1 :=
    Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hf.1) hnu
  have hdimS : ringKrullDim (MvPolynomial (Fin k × Fin n) F) = ((k * n : ℕ) : WithBot ℕ∞) := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add,
      Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  have hform := GroundTheory.Arith.Abelian.Jacobian.height_add_ringKrullDim_quotient F (Ideal.span {f})
  rw [hht, hdimS] at hform
  have := hP.isPrime
  obtain ⟨m, hm, -⟩ :=
    GroundTheory.Arith.Abelian.Jacobian.exists_ringKrullDim_eq_trdeg (k := F) (A := MvPolynomial (Fin n) F ⧸ P)
  cases m with
  | zero =>
    exfalso
    have : Ring.KrullDimLE 0 (MvPolynomial (Fin n) F ⧸ P) := Ring.krullDimLE_iff.mpr (by rw [hm])
    exact hP.not_isField_quotient Ring.KrullDimLE.isField_of_isDomain
  | succ d =>
    have h := h₁ F n k d P hP hm
    rw [hspan] at h
    rw [h] at hform
    have h3 : ((1 + (k * n - k + min k d) : ℕ) : WithBot ℕ∞) = ((k * n : ℕ) : WithBot ℕ∞) := by
      rw [Nat.cast_add, Nat.cast_one]
      convert hform using 2
      exact WithBot.coe_one.symm
    replace h3 := Nat.cast_injective h3
    rw [hm]
    congr 1
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      omega
    · have hkn := Nat.le_mul_of_pos_right k hn
      generalize k * n = N at h3 hkn
      omega

end GroundTheory.Heights₂.Heights
