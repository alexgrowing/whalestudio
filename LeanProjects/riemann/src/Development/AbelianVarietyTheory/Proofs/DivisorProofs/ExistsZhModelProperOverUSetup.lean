import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyUWit
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ZarhinNormalProjectiveModelExistsProof
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveLatticeTwistGenerated
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomExtOfIsOpenImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibrePreconnected
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteClosureThetaRatiosOfIsCl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsIsoMorphismRestrictOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftOfIsProperOfIsHomId
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.UPoinc.exists_zhModel_proper_over_uSetup : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf), ∀ (X : USetup C), IsProjOver X.M.s → ∃ (Y : RatModel X.o₁ X.Ω₁) (U₀ : Y.Z.Opens) (EE : Y.Lat X.S.J) (_ : ZHOut X.ρ Y U₀ EE) (q : Y.Z ⟶ X.M.Z), X.S.Over₀ Y U₀ ∧ X.S.IsEE Y U₀ EE ∧ IsProper q ∧ Y.pt ≫ q = X.M.pt ∧ (∀ z : X.M.Z, _root_.IsPreconnected (q.base ⁻¹' {z})) ∧ ∀ (p : ℕ) [Fact p.Prime] (z : X.M.Z) (ct : UCTrait X p z), ∃ y : Sp (OO p) ⟶ Y.Z, y ≫ q = ct.y := by
  intro E _ _ _ H Dw _ l Xo cf C X₁ hproj
  obtain ⟨m, c, hc⟩ := RatModel.exists_isCl_of_isProjOver hproj
  have hc0 : ∃ j, c j ≠ 0 := by
    obtain ⟨j, hj⟩ := hc.1 (genericPoint X₁.M.Z)
    exact ⟨j, hj.1⟩
  obtain ⟨Y, U₀, EE, hO, hdiv, hE, ⟨G⟩⟩ := GlobalTheory.zhSt_holds X₁.o₁ X₁.Ω₁ X₁.S X₁.ρ X₁.big (Fin (m + 1)) c hc0
    (GlobalTheory.ZH.finite_closure_theta_ratios_of_isCl X₁.o₁ X₁.Ω₁ X₁.S X₁.M (Fin (m + 1)) c hc)
  obtain ⟨q, hq⟩ := hc.exists_isHom (M' := Y) (φ := AlgHom.id X₁.o₁ X₁.Ω₁) hdiv
  have hYp : IsProper Y.s := ((GlobalTheory.isProjOver_iff_isProper_and_exists_isAmpleLB _).1 hO.proj).1
  have hsep : IsSeparated X₁.M.s := X₁.M.sep
  have hqp : IsProper q := by
    haveI : IsProper (q ≫ X₁.M.s) := by rw [hq.inducedModelMorphism_comp_structureMap]; exact hYp
    exact IsProper.of_comp q X₁.M.s
  have hpt : Y.pt ≫ q = X₁.M.pt :=
    hq.trans ((congrArg (· ≫ X₁.M.pt) (Spec.map_id _)).trans (Category.id_comp _))
  refine ⟨Y, U₀, EE, G, q, hO, hE, hqp, hpt, ?_, ?_⟩
  · obtain ⟨U, hU, hiso⟩ := GlobalTheory.ZH.RatModel.exists_isIso_morphismRestrict_of_isProjOver X₁.o₁ X₁.Ω₁ Y X₁.M hO.proj q hq
    have : IsDedekindDomain X₁.o₁ := (inferInstance : ArithBase X₁.o₁ X₁.Ω₁).ded
    have := X₁.M.lft
    have : IsLocallyNoetherian X₁.M.Z := LocallyOfFiniteType.isLocallyNoetherian X₁.M.s
    exact GlobalTheory.ZariskiConn.fibre_preconnected Y.Z X₁.M.Z q (fun x => ⟨X₁.normal.isDomain_stalk x, X₁.normal.isIntegrallyClosed_stalk x⟩) U hU hiso
  · intro p _ z₁ ct
    exact GlobalTheory.exists_lift_of_isProper_of_isHom_id X₁.o₁ X₁.Ω₁ Y X₁.M q hq hqp p ct.y
