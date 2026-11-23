import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortExactVectorBundlesRankAdd
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.GenericFiniteMaps
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LB (toMod)
open GlobalTheory.VB
open GlobalTheory.IndefiniteRowSideFullHecke.GenericFiniteMaps
open GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.short_exact_vector_bundles_rank_add : ∀ (X : Scheme.{0}) (S : ShortComplex X.Modules) (r s : ℕ), S.ShortExact → IsVB S.X₁ r → IsVB S.X₃ s → IsVB S.X₂ (r + s) := by
  first | exact @GlobalTheory.VBExt.isVB_X₂_of_shortExact | exact GlobalTheory.VBExt.isVB_X₂_of_shortExact | (intros; apply GlobalTheory.VBExt.isVB_X₂_of_shortExact <;> assumption)
