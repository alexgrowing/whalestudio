import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.XTwApplyApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.DualKer
import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.LenDual

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Tower

theorem UpperTheory.V.Tower.cokerDual :
    ∀ (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Module ℤ_[l] M] (g : Module.End ℤ_[l] M) (t : Module.End ℤ_[l] (M →ₗ[ℤ_[l]] QZ l)), (∀ x φ, t x φ = x (g φ)) →
        cokerLen t = Module.length ℤ_[l] (LinearMap.ker g) := by
  intro l _ M _ _ g t h
  have ht : t = LinearMap.lcomp ℤ_[l] (QZ l) g := LinearMap.ext fun x => LinearMap.ext fun φ => h x φ
  obtain ⟨h1, h2⟩ := UpperTheory.V.Tower.dualKer l M M g
  have hr : LinearMap.range t
      = LinearMap.ker (LinearMap.lcomp ℤ_[l] (QZ l) (LinearMap.ker g).subtype) := by
    rw [ht]; exact h1
  rw [← UpperTheory.V.Tower.lenDual l (LinearMap.ker g)]
  exact ((Submodule.quotEquivOfEq _ _ hr).trans
    (LinearMap.quotKerEquivOfSurjective _ (h2 (LinearMap.ker g)))).length_eq
