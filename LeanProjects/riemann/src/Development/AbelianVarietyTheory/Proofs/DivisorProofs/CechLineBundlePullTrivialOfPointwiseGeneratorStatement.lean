import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechLineBundlePullTrivialOfPointwiseGenerator
import Development.AbelianVarietyTheory.Definitions.Divisors.PtAlgSpOver
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cechLineBundle_pull_trivial_of_pointwiseGenerator : ∀ (R : Type) [CommRing R] (X Y : Over (Sp R)) (L : LB X.left), L.IsLB → ∀ (q : Y ⟶ X) (t : ∀ (E : Type) [CommRing E] [Algebra R E], Pt Y E → L.ι → E), IsPtGen L q t → GlobalTheory.AbLaw.Triv (L.pull q.left) := by
  first | exact @GlobalTheory.PtExt.triv_pull_of_isPtGen | exact GlobalTheory.PtExt.triv_pull_of_isPtGen | (intros; apply GlobalTheory.PtExt.triv_pull_of_isPtGen <;> assumption)
