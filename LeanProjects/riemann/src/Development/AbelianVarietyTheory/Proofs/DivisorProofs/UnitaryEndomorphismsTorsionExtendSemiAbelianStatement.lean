import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryEndomorphismsTorsionExtendSemiAbelian
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorsExt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.FibLat
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryEndomorphisms_torsion_extend_semiAbelian : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf) (X : USetup C) (wi : UWit X) (Y : RatModel X.o₁ X.Ω₁) (U₀ : Y.Z.Opens) (EE : Y.Lat X.S.J) (FinalForm : ZHOut X.ρ Y U₀ EE) (q : Y.Z ⟶ X.M.Z), X.S.Over₀ Y U₀ → X.S.IsEE Y U₀ EE → Y.pt ≫ q = X.M.pt → ∀ z : X.M.Z, X.S.TT X.M z ≤ X.S.HH X.M z → ∃ (f : 𝓞 E → (FinalForm.G ⟶ FinalForm.G)) (gγ : X.S.TT X.M z → (Over.mk Y.pt ⟶ FinalForm.G)), GlobalTheory.UPoinc.GFib.IsEndoExt X wi FinalForm f ∧ GlobalTheory.UPoinc.GFib.IsTorsExt X wi FinalForm q z gγ := by
  first | exact @GlobalTheory.UPoinc.GFib.endo_torsion_ext | exact GlobalTheory.UPoinc.GFib.endo_torsion_ext | (intros; apply GlobalTheory.UPoinc.GFib.endo_torsion_ext <;> assumption)
