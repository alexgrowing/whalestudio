import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPeriodFormAutomorphismUnitaryLabellings
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_periodForm_automorphism_unitary_labellings : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf) (X : USetup C) (p : ℕ) [Fact p.Prime] (z : X.M.Z) (ct : UCTrait X p z) (yy yy' : X.S.Gam →+ ModN (X.S.r * X.S.N) ct.T.P.D.toPre.X), UIsLab X ct yy → UIsLab X ct yy' → ∃ κ : ct.T.P.D.toPre.X ≃+ ct.T.P.D.toPre.X, (∀ x, ct.T.be (κ x) (κ x) = ct.T.be x x) ∧ ∀ a μ, yy a = QuotientAddGroup.mk μ → yy' a = QuotientAddGroup.mk (κ μ) := by
  first | exact @GlobalTheory.UPoinc.ULabUniq.main | exact GlobalTheory.UPoinc.ULabUniq.main | (intros; apply GlobalTheory.UPoinc.ULabUniq.main <;> assumption)
