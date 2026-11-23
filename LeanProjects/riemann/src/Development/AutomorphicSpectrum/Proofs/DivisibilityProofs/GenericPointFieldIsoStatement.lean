import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.GenericPointFieldIso
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.RootOnFund
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_point_field_iso : ∀ (X : Scheme.{0}) (Ω Ω' : Type) [Field Ω] [Field Ω'] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (ξ' : Spec (CommRingCat.of Ω') ⟶ X), IsCptGen ξ → IsCptGen ξ' → genPt ξ = genPt ξ' → ∃ ψ : Ω' ≃+* Ω, spMap ψ.toRingHom ≫ ξ' = ξ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GenIso.exists_iso_of_genPt_eq | exact GlobalTheory.CompanionTheory.Ar.GenIso.exists_iso_of_genPt_eq | (intros; apply GlobalTheory.CompanionTheory.Ar.GenIso.exists_iso_of_genPt_eq <;> assumption)
