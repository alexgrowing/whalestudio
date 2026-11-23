import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterLatticeUnitaryClassicalTraitCentre
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
theorem _root_.GlobalTheory.T.characterLattice_unitaryClassicalTrait_centre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf) (X : USetup C) (wi : UWit X) (Y : RatModel X.o₁ X.Ω₁) (U₀ : Y.Z.Opens) (EE : Y.Lat X.S.J) (FinalForm : ZHOut X.ρ Y U₀ EE) (q : Y.Z ⟶ X.M.Z), X.S.Over₀ Y U₀ → X.S.IsEE Y U₀ EE → IsProper q → Y.pt ≫ q = X.M.pt → ∀ (p : ℕ) [Fact p.Prime] (z : X.M.Z) (f : 𝓞 E → (FinalForm.G ⟶ FinalForm.G)) (gγ : X.S.TT X.M z → (Over.mk Y.pt ⟶ FinalForm.G)), GlobalTheory.UPoinc.GFib.IsEndoExt X wi FinalForm f → GlobalTheory.UPoinc.GFib.IsTorsExt X wi FinalForm q z gγ → ∀ ζ : X.o₁ˣ, IsPrimitiveRoot (ζ : X.o₁) (X.S.r * X.S.N) → ∃ (s : ZMod (X.S.r * X.S.N)) (σ : 𝓞 E → 𝓞 E), IsUnit s ∧ Function.Surjective σ ∧ ∀ (ct : UCTrait X p z) (y : Sp (OO p) ⟶ Y.Z), y ≫ q = ct.y → ∀ (yy : X.S.Gam →+ ModN (X.S.r * X.S.N) ct.T.P.D.toPre.X), UIsLabW X wi ct yy → ∃ c : X.S.TT X.M z → ct.T.P.D.toPre.X →+ ZMod (X.S.r * X.S.N), LatAt f gγ ζ (X.S.r * X.S.N) (fun a => DistribSMul.toAddMonoidHom ct.T.P.D.toPre.X (σ a)) c (y (cPt p)) ∧ ∀ (a : X.S.Gam) (v : ct.T.P.D.toPre.X) (t : X.S.TT X.M z), yy a = QuotientAddGroup.mk v → c t v = s * eStd X.S.g _ (t : X.S.Gam) a := by
  first | exact @GlobalTheory.UPoinc.GFibCentre.latAt_centre | exact GlobalTheory.UPoinc.GFibCentre.latAt_centre | (intros; apply GlobalTheory.UPoinc.GFibCentre.latAt_centre <;> assumption)
