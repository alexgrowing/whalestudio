import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualFrameTransitionCoefficients
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenImmersionChart
open CategoryTheory Limits AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_frame_transition_coefficients : ∀ (X : Scheme.{0}) (F : X.Modules) (r : ℕ) (V V' : X.Opens) (e : Fin r → Γ(F, V)) (s : Fin r → Γ(F, V')) (he : GlobalTheory.VB.IsFrame e) (hs : GlobalTheory.VB.IsFrame s) (l i : Fin r), GlobalTheory.ChainPts.coef true he.dual hs.dual l i = GlobalTheory.ChainPts.coef false he hs l i := by
  first | exact @GlobalTheory.ChainPts.coef_dual | exact GlobalTheory.ChainPts.coef_dual | (intros; apply GlobalTheory.ChainPts.coef_dual <;> assumption)
