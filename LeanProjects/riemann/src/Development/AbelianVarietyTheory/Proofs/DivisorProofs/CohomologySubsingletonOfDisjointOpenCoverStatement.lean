import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologySubsingletonOfDisjointOpenCover
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageOfIsPullback
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Definitions.Divisors.SameDiv
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cohomology_subsingleton_of_disjoint_open_cover : ∀ (X : Scheme.{0}) (M : LB X) (κ : Type) (U : κ → X.Opens), M.IsLB → ⨆ c, U c = ⊤ → (Pairwise fun a b => Disjoint (U a) (U b)) → ∀ q : ℕ, (∀ c, Subsingleton (coh (LB.toMod (M.pull (U c).ι)) q)) → Subsingleton (coh (LB.toMod M) q) := by
  first | exact @GlobalTheory.coh_subsingleton_of_disjoint_cover | exact GlobalTheory.coh_subsingleton_of_disjoint_cover | (intros; apply GlobalTheory.coh_subsingleton_of_disjoint_cover <;> assumption)
