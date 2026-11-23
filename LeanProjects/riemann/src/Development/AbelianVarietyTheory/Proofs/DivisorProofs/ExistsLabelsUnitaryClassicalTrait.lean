import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyUWit
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRechartingThetaSystemAffineOpenStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RechartAtUnitaryClassicalTraitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisedModelLabelsUnitaryTraitStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.UPoinc

theorem exists_uIsLabW : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf), ∀ (X : USetup C) (wi : UWit X) (p : ℕ) [Fact p.Prime] (z : X.M.Z) (ct : UCTrait X p z), ∃ yy : X.S.Gam →+ ModN (X.S.r * X.S.N) ct.T.P.D.toPre.X, UIsLabW X wi ct yy := by
  intro E _ _ _ H Dw hpq l Xo cf C X wi p _ z ct
  have hw : X.π ((gPt p ≫ ct.y) (closedPoint (PadicAlgCl p))) ∈ Set.range C.i := by
    refine ⟨(spMap ct.ι ≫ ct.T.y) (closedPoint (PadicAlgCl p)), ?_⟩
    have e := congrArg (fun f : Sp (PadicAlgCl p) ⟶ C.Z => f (closedPoint (PadicAlgCl p))) ct.comm
    simp only [Scheme.Hom.comp_apply] at e ⊢
    exact e.symm
  obtain ⟨U, c₀, hc, fg, frac, hth, hev, ρ', u', hU, hwU, hsame, hi₀, hpt, G, hG, α, β, hα, hβ, hL, hm⟩ :=
    GlobalTheory.T.exists_recharting_thetaSystem_affineOpen E H Dw hpq l Xo cf C X wi _ hw
  obtain ⟨hle, y₁, hy₁, hpt₁, hint⟩ := GlobalTheory.T.rechart_at_unitaryClassicalTrait E H Dw hpq l Xo cf C X p z ct U u' hU hwU hpt
  obtain ⟨u, lb, j, hq, hcong⟩ :=
    GlobalTheory.T.exists_uniformisedModel_labels_unitaryTrait E H Dw hpq l Xo cf X.o₁ X.Ω₁ _ ρ' u' G hG α β hα hβ hL p y₁ ct.T ct.ι ct.int hpt₁ hint
  let jm : ModN (X.S.r * X.S.N) u.D.toPre.X →+ ModN (X.S.r * X.S.N) ct.T.P.D.toPre.X :=
    QuotientAddGroup.map _ _ j.toAddMonoidHom (by
      rintro _ ⟨x, rfl⟩
      exact ⟨j x, by simp⟩)
  refine ⟨jm.comp lb.yy, c₀, hc, X.M.ringOn U, fg, frac, hth, hev, ρ', u', hsame, hi₀, hpt, hle, G, hG, α, β, hα, hβ, hL,
    hm, y₁.comp (toRat _), hy₁, u, lb, j, hq, ?_, hcong⟩
  intro a χ ha
  simp only [AddMonoidHom.comp_apply, ha, jm]
  rfl

end GlobalTheory.UPoinc
