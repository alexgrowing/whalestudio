import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentOfChartFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.GrNormCompCast
open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.QCoh GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ChainPts
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_of_chart_frame : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p} (Z : LocM.Mdl Y i₀) (a : Fin Z.m) (k : Type) [CommRing k] (φ : Γ(Z.X, (Z.U a).1) →+* k) (y : Sp k ⟶ Z.X), spMap φ ≫ Z.chart a = y → ∀ x : Letter Dw, IsTanAtG (Y Z.i).t (y ≫ Z.π) ((Z.fr a).bc φ x.1 x.2) := by
  first | exact @GlobalTheory.ChainPts.FrameTan.isTanAtG_frame_bc | exact GlobalTheory.ChainPts.FrameTan.isTanAtG_frame_bc | (intros; apply GlobalTheory.ChainPts.FrameTan.isTanAtG_frame_bc <;> assumption)
