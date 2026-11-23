import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualNumberGeneratorOfTorsorCoboundary
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
theorem _root_.GlobalTheory.T.exists_dualNumberGenerator_of_torsorCoboundary : ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (P : LB (A ⊗ B).left), P.IsLB → ∀ v : epsR R ⟶ B, IsTangent v → ∀ (j : ∀ (D : Type) [CommRing D] [Algebra R D], Pt A D → P.ι), IsChoice P j → ∀ s, IsPtGen P (AbDual.inl A B) s → ∀ k : Fn0 A, IsCob (chartsA P) (tanCoc P j v) k → ∃ T, IsEpsGen P v T := by
  first | exact @GlobalTheory.PtExt.exists_isEpsGen_of_isCob | exact GlobalTheory.PtExt.exists_isEpsGen_of_isCob | (intros; apply GlobalTheory.PtExt.exists_isEpsGen_of_isCob <;> assumption)
