import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartPullbackLineBundleTransitionEqAppLE
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartFrameBaseHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartPullback_lineBundle_transition_eq_appLE : ∀ (Y Y' : Scheme.{0}) (A' : LB Y') (A : LB Y) (h : Y' ⟶ Y) (cp : ChartPull A' A h) (i j : A'.ι), ((A'.g i j : Γ(Y', A'.U i ⊓ A'.U j)ˣ) : Γ(Y', A'.U i ⊓ A'.U j)) = (h.appLE (A.U (cp.idx i) ⊓ A.U (cp.idx j)) (A'.U i ⊓ A'.U j) (le_inf (inf_le_left.trans (cp.le i)) (inf_le_right.trans (cp.le j)))).hom ((A.g (cp.idx i) (cp.idx j) : Γ(Y, A.U (cp.idx i) ⊓ A.U (cp.idx j))ˣ) : Γ(Y, A.U (cp.idx i) ⊓ A.U (cp.idx j))) := by
  first | exact @GlobalTheory.chartPull_g_appLE | exact GlobalTheory.chartPull_g_appLE | (intros; apply GlobalTheory.chartPull_g_appLE <;> assumption)
