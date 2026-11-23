import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AlgebraMapMemMaximalRealSubfieldIff
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsSqrtTotallyNegative
open NumberField

open scoped IntermediateField

namespace GlobalTheory.CMSqrtNeg

theorem finrank_adjoin_sq {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] (c : E) (t : Ω)
    (ht : t ^ 2 = algebraMap E Ω c) (hn : t ∉ Set.range (algebraMap E Ω)) :
    IsIntegral E t ∧ Module.finrank E E⟮t⟯ = 2 := by
  have hm : (Polynomial.X ^ 2 - Polynomial.C c).Monic := Polynomial.monic_X_pow_sub_C c two_ne_zero
  have h0 : Polynomial.aeval t (Polynomial.X ^ 2 - Polynomial.C c) = 0 := by simp [ht]
  have hi : IsIntegral E t := ⟨_, hm, by simpa [Polynomial.aeval_def] using h0⟩
  refine ⟨hi, ?_⟩
  rw [IntermediateField.adjoin.finrank hi]
  have h1 : (minpoly E t).natDegree ≤ 2 := by
    have := Polynomial.natDegree_le_of_dvd (minpoly.dvd E t h0) hm.ne_zero
    rwa [Polynomial.natDegree_X_pow_sub_C] at this
  have h2 : 2 ≤ (minpoly E t).natDegree := (minpoly.two_le_natDegree_iff hi).2 (by simpa using hn)
  omega

theorem exists_qcm_adjoin_sqrt_neg : ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (p : ℕ), 0 < p → ∀ δ : Ω, δ ^ 2 = -(p : Ω) → δ ∉ Set.range (algebraMap E Ω) →
    ∃ Q : GlobalTheory.RealGal.QCM E Ω, Q.K = IntermediateField.adjoin E {δ} := by
  intro E Ω _ _ _ _ _ _ p hp δ hδ hδn
  have hδ' : δ ^ 2 = algebraMap E Ω (-(p : E)) := by simp [hδ]
  obtain ⟨hint, htwo⟩ := finrank_adjoin_sq (-(p : E)) δ hδ' hδn
  haveI : FiniteDimensional E E⟮δ⟯ := IntermediateField.adjoin.finiteDimensional hint
  haveI nf : NumberField E⟮δ⟯ := NumberField.of_module_finite E _
  obtain ⟨d, s, hs, hsn, hneg⟩ := GlobalTheory.CMGen.exists_sqrt_totallyNegative E
  have hs0 : s ≠ 0 := fun h => hsn (h ▸ zero_mem _)
  let t : E⟮δ⟯ := ⟨δ * algebraMap E Ω s,
    mul_mem (IntermediateField.subset_adjoin E {δ} rfl) (IntermediateField.algebraMap_mem _ s)⟩
  let d' : maximalRealSubfield E := -(p : maximalRealSubfield E) * (d : maximalRealSubfield E)
  have ht : t ^ 2 = algebraMap E E⟮δ⟯ (algebraMap (maximalRealSubfield E) E d') := by
    apply Subtype.ext
    show (δ * algebraMap E Ω s) ^ 2 = algebraMap E Ω (algebraMap (maximalRealSubfield E) E d')
    rw [mul_pow, hδ, ← map_pow, hs]
    simp [d']
  have htn : t ∉ Set.range (algebraMap E E⟮δ⟯) := by
    rintro ⟨e, he⟩
    apply hδn
    refine ⟨e * s⁻¹, ?_⟩
    have h1 : algebraMap E Ω e = δ * algebraMap E Ω s := congrArg Subtype.val he
    have h2 : algebraMap E Ω s ≠ 0 := (map_ne_zero _).2 hs0
    rw [map_mul, h1, map_inv₀, mul_assoc, mul_inv_cancel₀ h2, mul_one]
  have hpos : ∀ φ : maximalRealSubfield E →+* ℝ, 0 < φ d' := fun φ => by
    have := hneg φ
    have hp' : (0 : ℝ) < p := by exact_mod_cast hp
    simp only [d', map_mul, map_neg, map_natCast]
    nlinarith
  have hcm := (GlobalTheory.isCMField_of_sq_eq_totallyPositive E E⟮δ⟯ htwo d' t ht htn hpos).1
  exact ⟨⟨E⟮δ⟯, nf, hcm, htwo⟩, rfl⟩

end GlobalTheory.CMSqrtNeg
