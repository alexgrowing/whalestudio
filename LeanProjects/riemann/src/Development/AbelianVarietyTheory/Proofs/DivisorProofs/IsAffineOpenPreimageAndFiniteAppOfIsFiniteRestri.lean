import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

namespace GlobalTheory

theorem isAffineOpen_preimage_and_finite_app_of_isFinite_restrict :
    ∀ (X Z : Scheme.{0}) (φ : X ⟶ Z) (V : Z.Opens), IsAffineOpen V → IsFinite (φ ∣_ V) →
      IsAffineOpen (φ ⁻¹ᵁ V) ∧ (φ.app V).hom.Finite := by
  intro X Z φ V hV hf
  haveI : IsAffine (V : Scheme) := hV
  have h1 : IsAffine (φ ⁻¹ᵁ V : Scheme) := isAffine_of_isAffineHom (φ ∣_ V)
  refine ⟨h1, ?_⟩
  have h2 := hf.finite_app ⊤ (isAffineOpen_top _)
  rw [morphismRestrict_app] at h2
  have e : V.ι ''ᵁ ⊤ = V := by simp
  rw [← e]
  exact (RingHom.finite_respectsIso.cancel_right_isIso _ _).mp h2

end GlobalTheory
