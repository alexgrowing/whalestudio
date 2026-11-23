import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLifted
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCoordinatesStalkFlat
open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.LogPair GlobalTheory.Cartier ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.GlobalTheory.T.etale_coordinates_stalk_flat : ∀ {R : Type} [CommRing R] {Y : Scheme.{0}} (g : Y ⟶ Sp R) (U : Y.Opens) {n : ℕ} (t : Fin n → Γ(Y, U)), IsAffineOpen U → IsEtCoord g U t → ∀ (y : Y) (hy : y ∈ U), ((Y.presheaf.germ U y hy).hom.comp (cstOn g U)).Flat := by
  first | exact @_root_.GlobalTheory.LogPair.flat_germ_comp_cstOn_of_isEtCoord | exact _root_.GlobalTheory.LogPair.flat_germ_comp_cstOn_of_isEtCoord | (intros; apply _root_.GlobalTheory.LogPair.flat_germ_comp_cstOn_of_isEtCoord <;> assumption)
