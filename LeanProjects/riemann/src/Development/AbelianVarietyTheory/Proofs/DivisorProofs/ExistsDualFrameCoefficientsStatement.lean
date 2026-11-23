import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualFrameCoefficients
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenImmersionChart
open CategoryTheory Limits AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dual_frame_coefficients : ∀ (X : Scheme.{0}) (F : X.Modules) (n r : ℕ), GlobalTheory.VB.IsVB F n → ∀ (V : X.Opens) (e : Fin r → Γ(GlobalTheory.VB.dual F, V)) (he : GlobalTheory.VB.IsFrame e), ∃ (e' : Fin r → Γ(F, V)) (he' : GlobalTheory.VB.IsFrame e'), ∀ (V' : X.Opens) (s : Fin r → Γ(F, V')) (hs : GlobalTheory.VB.IsFrame s) (l i : Fin r), GlobalTheory.ChainPts.coef true he hs.dual l i = GlobalTheory.ChainPts.coef false he' hs l i := by
  first | exact @GlobalTheory.ChainPts.exists_frame_coef_dual_eq | exact GlobalTheory.ChainPts.exists_frame_coef_dual_eq | (intros; apply GlobalTheory.ChainPts.exists_frame_coef_dual_eq <;> assumption)
