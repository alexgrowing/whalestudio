import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentFrameAtIntegralPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenImmersionChart
open CategoryTheory Limits AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_frame_at_integral_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p) (Z : GlobalTheory.LocM.Mdl Y i₀) (X : Scheme.{0}) (h : X ⟶ Z.X) (r : ℕ) (x : Fin r → Letter Dw), Function.Bijective x → ∀ (hfr : ∀ a, GlobalTheory.VB.IsFrame (GlobalTheory.TanSec.secX Z h x a)) (y : Z.Pt) (w : Sp ↥(intO ↥y.C.S) ⟶ X), w ≫ h = y.z → ∀ (a : Fin Z.m) (φ : Γ(Z.X, (Z.U a).1) →+* ↥y.C.S), spMap φ ≫ Z.chart a = y.gen → ∀ (V : X.Opens) (e : Fin r → Γ(GlobalTheory.TanSec.lieX Z h, V)) (he : GlobalTheory.VB.IsFrame e), ⊤ ≤ w ⁻¹ᵁ V → ∀ (cf : Fin r → ↥y.C.S) (v : Sp (DualNumber ↥y.C.S) ⟶ (Y Z.i).t.G.left), IsCombAtG (Y Z.i).t (y.gen ≫ Z.π) (fun i => (Z.fr a).bc φ (x i).1 (x i).2) cf v → (v ∈ lat (Y Z.i).t p (y.gen ≫ Z.π) false ↔ ∀ l, ‖∑ i, cf i * valF (spMap (intO ↥y.C.S).subtype ≫ w) _ (GlobalTheory.ChainPts.coef false he (hfr a) l i)‖ ≤ 1) := by
  first | exact @GlobalTheory.TanSec.Norm.mem_lat_iff_coef | exact GlobalTheory.TanSec.Norm.mem_lat_iff_coef | (intros; apply GlobalTheory.TanSec.Norm.mem_lat_iff_coef <;> assumption)
