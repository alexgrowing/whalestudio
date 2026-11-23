import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HeightOnePrimeDvrStalk
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SpecStalkSpecializesComp
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.LieStalk
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.height_one_prime_dvr_stalk : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X), IsCptGen ξ → IsLocallyNoetherian X → IsNormalScheme X → ∀ (p : Cpt ξ) (P : PrimeSpectrum (regAt ξ p)), P.asIdeal.height = 1 → ∃ (q : Cpt ξ) (hs : q.1 ⤳ p.1), (∃ _ : IsDomain (X.presheaf.stalk q.1), IsDiscreteValuationRing (X.presheaf.stalk q.1)) ∧ (∀ s : regAt ξ p, s ∉ P.asIdeal → (s : Ω)⁻¹ ∈ regAt ξ q) ∧ ∀ a ∈ regAt ξ q, ∃ s : regAt ξ p, s ∉ P.asIdeal ∧ (s : Ω) * a ∈ regAt ξ p := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LieStalk.HeightOne.exists_generisation_of_height_eq_one | exact GlobalTheory.CompanionTheory.Ar.LieStalk.HeightOne.exists_generisation_of_height_eq_one | (intros; apply GlobalTheory.CompanionTheory.Ar.LieStalk.HeightOne.exists_generisation_of_height_eq_one <;> assumption)
