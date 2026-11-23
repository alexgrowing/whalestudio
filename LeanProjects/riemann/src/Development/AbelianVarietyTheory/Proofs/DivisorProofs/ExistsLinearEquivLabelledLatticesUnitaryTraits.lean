import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabelledUnitaryTraitsLatticesEquivConnectedFibreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsZhModelProperOverUSetup
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyUWit
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.UPoinc.exists_linearEquiv_labelled_of_uIsLabW : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf), ∀ (X : USetup C) (wi : UWit X), IsProjOver X.M.s → ∀ (p : ℕ) [Fact p.Prime] (z : X.M.Z) (ct ct' : UCTrait X p z) (yy : X.S.Gam →+ ModN (X.S.r * X.S.N) ct.T.P.D.toPre.X) (yy' : X.S.Gam →+ ModN (X.S.r * X.S.N) ct'.T.P.D.toPre.X), UIsLabW X wi ct yy → UIsLabW X wi ct' yy' → ∃ e : ct.T.P.D.toPre.X ≃ₗ[𝓞 E] ct'.T.P.D.toPre.X, ∀ a μ, yy a = QuotientAddGroup.mk μ → yy' a = QuotientAddGroup.mk (e μ) := by
  intro E _ _ _ H Dw hpq l Xo cf C X wi hproj p _ z ct ct' yy yy' hl hl'
  obtain ⟨Y, U₀, EE, G, q, hO, hE, hqp, hpt, hconn, hlift⟩ :=
    GlobalTheory.UPoinc.exists_zhModel_proper_over_uSetup E H Dw hpq l Xo cf C X hproj
  obtain ⟨y, hy⟩ := hlift p z ct
  obtain ⟨y', hy'⟩ := hlift p z ct'
  obtain ⟨θ, hθ, hsm⟩ := GlobalTheory.T.labelledUnitaryTraits_lattices_equiv_connectedFibre E H Dw hpq l Xo cf C X wi Y U₀ EE G q hO hE hqp hpt p z (hconn z)
    ct ct' y y' hy hy' yy yy' hl hl'
  exact ⟨θ.toLinearEquiv hsm, hθ⟩
