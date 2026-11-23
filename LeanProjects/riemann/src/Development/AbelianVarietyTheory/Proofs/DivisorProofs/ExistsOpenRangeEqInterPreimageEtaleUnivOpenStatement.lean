import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenRangeEqInterPreimageEtaleUnivOpen
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_open_range_eq_inter_preimage_etale_univOpen : ∀ (X B T Z : Scheme.{0}) (c : X ⟶ B) (j : T ⟶ B) (i : Z ⟶ X) (φ : Z ⟶ T), Etale c → IsPreimmersion j → UniversallyOpen φ → i ≫ c = φ ≫ j → ∃ W : X.Opens, Set.range i = (W : Set X) ∩ c ⁻¹' Set.range j := by
  first | exact @GlobalTheory.Mum.exists_opens_range_eq_of_etale | exact GlobalTheory.Mum.exists_opens_range_eq_of_etale | (intros; apply GlobalTheory.Mum.exists_opens_range_eq_of_etale <;> assumption)
