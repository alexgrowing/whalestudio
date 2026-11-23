import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentFrameAtFieldPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenImmersionChart
open CategoryTheory Limits AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_frame_at_field_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p) (Z : GlobalTheory.LocM.Mdl Y i₀) (X : Scheme.{0}) (h : X ⟶ Z.X) (r : ℕ) (x : Fin r → Letter Dw), Function.Bijective x → ∀ (hfr : ∀ a, GlobalTheory.VB.IsFrame (GlobalTheory.TanSec.secX Z h x a)) (k : Type) [Field k] (w : Sp k ⟶ X) (a a' : Fin Z.m) (φ : Γ(Z.X, (Z.U a).1) →+* k) (φ' : Γ(Z.X, (Z.U a').1) →+* k), spMap φ ≫ Z.chart a = w ≫ h → spMap φ' ≫ Z.chart a' = w ≫ h → ∀ j, IsCombAtG (Y Z.i).t (w ≫ h ≫ Z.π) (fun i => (Z.fr a).bc φ (x i).1 (x i).2) (fun i => valF w _ (GlobalTheory.ChainPts.coef false (hfr a) (hfr a') i j)) ((Z.fr a').bc φ' (x j).1 (x j).2) := by
  first | exact @GlobalTheory.TanSec.Glue.isCombAtG_coef | exact GlobalTheory.TanSec.Glue.isCombAtG_coef | (intros; apply GlobalTheory.TanSec.Glue.isCombAtG_coef <;> assumption)
