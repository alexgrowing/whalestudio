import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerTransformProperties
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CstD
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open Ad3.R (G2 Jd md Dt KA Set0 Coord LInv pt dia2 pri)
open GlobalTheory.CompanionTheory.UnfoldingAlt
open scoped NumberField.AdeleRing ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittaker_transform_properties : (∀ (W : G3 → ℂ) (g : G3), tr W g = W (w3 * ti (dia dl3) * ti g)) ∧
  (∀ (W : G3 → ℂ) (h g : G3), tr W (g * h) = tr (fun x => W (x * ti h)) g) ∧
  Function.Injective tr ∧
  (∀ W : G3 → ℂ, (∀ x y z g, W (uni x y z * g) = (adelicChar ℚ (x + z) : ℂ) * W g) →
    ∀ x y z g, tr W (uni x y z * g) = (adelicChar ℚ (x + z) : ℂ) * tr W g) ∧
  (∀ W : G3 → ℂ, (∀ (a : (𝔸[ℚ])ˣ) g, W (dg a a a * g) = W g) → ∀ (a : (𝔸[ℚ])ˣ) g, tr W (dg a a a * g) = tr W g) := by
  first | exact @GlobalTheory.CompanionTheory.UnfoldingAlt.TrBasic.main | exact GlobalTheory.CompanionTheory.UnfoldingAlt.TrBasic.main | (intros; apply GlobalTheory.CompanionTheory.UnfoldingAlt.TrBasic.main <;> assumption)
