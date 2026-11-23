import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDominantGenericStalkOpen
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
open AlgebraicGeometry CategoryTheory Limits IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isDominant_generic_stalk_open : ∀ (X : Scheme.{0}) (x : X) [IsDomain (X.presheaf.stalk x)] (V O : X.Opens), x ∈ V →
    IsIntegral V.toScheme → O ≤ V → ∀ ι : Sp (FractionRing (X.presheaf.stalk x)) ⟶ O.toScheme,
    ι ≫ O.ι = jK (X.presheaf.stalk x) ≫ X.fromSpecStalk x → IsDominant ι := by
  first | exact @GlobalTheory.isDominant_fractionRing_stalk | exact GlobalTheory.isDominant_fractionRing_stalk | (intros; apply GlobalTheory.isDominant_fractionRing_stalk <;> assumption)
