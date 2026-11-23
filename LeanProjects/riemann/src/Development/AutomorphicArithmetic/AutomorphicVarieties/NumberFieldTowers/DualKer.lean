import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.XTwApplyApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.QzInj

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Tower

theorem UpperTheory.V.Tower.dualKer :
    ∀ (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Module ℤ_[l] M] (M' : Type) [AddCommGroup M'] [Module ℤ_[l] M'] (T : M →ₗ[ℤ_[l]] M'),
        LinearMap.range (LinearMap.lcomp ℤ_[l] (QZ l) T) = LinearMap.ker (LinearMap.lcomp ℤ_[l] (QZ l) (LinearMap.ker T).subtype) ∧
        ∀ p : Submodule ℤ_[l] M, Function.Surjective (LinearMap.lcomp ℤ_[l] (QZ l) p.subtype) := by
  intro l _ M _ _ M' _ _ T
  have hI := PropA.qzInj l
  refine ⟨?_, fun p g => ?_⟩
  · ext f
    rw [LinearMap.mem_range, LinearMap.mem_ker]
    constructor
    · rintro ⟨g, rfl⟩
      ext ⟨x, hx⟩
      simp only [LinearMap.lcomp_apply, LinearMap.comp_apply, Submodule.subtype_apply,
        LinearMap.zero_apply]
      rw [LinearMap.mem_ker.mp hx, map_zero]
    · intro hf
      have hle : LinearMap.ker T ≤ LinearMap.ker f := by
        intro x hx
        have := LinearMap.congr_fun hf ⟨x, hx⟩
        simpa using this
      let g0 : LinearMap.range T →ₗ[ℤ_[l]] QZ l :=
        ((LinearMap.ker T).liftQ f hle).comp (LinearMap.quotKerEquivRange T).symm.toLinearMap
      obtain ⟨h, hh⟩ := hI.out (LinearMap.range T).subtype Subtype.val_injective g0
      refine ⟨h, ?_⟩
      ext x
      simp only [LinearMap.lcomp_apply, LinearMap.comp_apply]
      have := hh ⟨T x, LinearMap.mem_range_self T x⟩
      simp only [Submodule.subtype_apply] at this
      rw [this]
      simp [g0, LinearMap.quotKerEquivRange_symm_apply_image]
  · obtain ⟨h, hh⟩ := hI.out p.subtype Subtype.val_injective g
    refine ⟨h, ?_⟩
    ext x
    simpa using hh x
