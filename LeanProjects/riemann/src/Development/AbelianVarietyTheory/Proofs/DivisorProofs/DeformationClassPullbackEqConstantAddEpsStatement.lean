import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeformationClassPullbackEqConstantAddEps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualMapCompDualMap
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deformation_class_pullback_eq_constant_add_eps : GlobalTheory.Published.AbelianDeRham → ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (i : A.left ⟶ A'.left) (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i) (g : ℕ), IsAbelianScheme A' → SmoothOfRelativeDimension g A'.hom → ∀ x : primDR A', ∃ b : primDR A, (liftMor (epsDP K) h).pull x = (constMor A).pull ((fibMor h).pull x) + (DualNumber.eps : DualNumber K) • (constMor A).pull b := by
  first | exact @GlobalTheory.CechKS.liftMor_pull_eq_const_add_eps | exact GlobalTheory.CechKS.liftMor_pull_eq_const_add_eps | (intros; apply GlobalTheory.CechKS.liftMor_pull_eq_const_add_eps <;> assumption)
