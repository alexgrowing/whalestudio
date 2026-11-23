import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRegularCoverOfAlteration

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

namespace GlobalTheory.FiniteOverProj

theorem isProjOver_of_isFinite_over :
    ∀ (A o : Type) [CommRing A] [CommRing o] (κ : A →+* o) (M Z : Scheme.{0}) (z : Z ⟶ Sp A) (π : M ⟶ Z) (s : M ⟶ Sp o), IsProjOver z → IsFinite π → IsNoetherianRing A → s ≫ spMap κ = π ≫ z → IsProjOver s := by
  intro A o _ _ κ M Z z π s hz hπ _ hs
  have h : IsProjOver (π ≫ z) := GlobalTheory.isProjOver_comp_of_isFinite π hz
  rw [← hs] at h
  exact GlobalTheory.RegCoverExists.isProjOver_of_comp_spMap κ h

end GlobalTheory.FiniteOverProj

end
