import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryApproxPoincareSeriesAtMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UValThruTopOfDisjoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryApproxPoincareSeriesAt_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (φ : InvFun (𝓞 E)) (d m : ℕ), 1 ≤ m → UApproxAt X₁ φ d → UApproxAt X₁ φ (d * m) := by
  first | exact @GlobalTheory.UPoinc.uApproxAt_mul | exact GlobalTheory.UPoinc.uApproxAt_mul | (intros; apply GlobalTheory.UPoinc.uApproxAt_mul <;> assumption)
