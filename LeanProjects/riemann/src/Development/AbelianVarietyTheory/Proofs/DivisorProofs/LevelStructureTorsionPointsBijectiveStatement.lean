import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelStructureTorsionPointsBijective
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMulVal
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Aff
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_structure_torsion_points_bijective : ∀ (R K : Type) [CommRing R] [Field K] [IsAlgClosed K] [Algebra R K] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (N : ℕ) (A : Type) [CommRing A] [HopfAlgebra R A] [Module.Finite R A] (θ : TorsPt G N A), IsLevel K θ → ∀ (B : Type) [CommRing B] [Algebra R B] [Algebra K B] [IsScalarTower R K B], Function.Bijective (θ.pt B) := by
  first | exact @GlobalTheory.GroupBplus.Aff.LevBij.level_bijective | exact GlobalTheory.GroupBplus.Aff.LevBij.level_bijective | (intros; apply GlobalTheory.GroupBplus.Aff.LevBij.level_bijective <;> assumption)
