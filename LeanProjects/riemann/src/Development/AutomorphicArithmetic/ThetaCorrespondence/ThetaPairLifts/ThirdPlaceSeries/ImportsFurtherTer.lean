import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmG2TwistSetup
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BoundAtTwoThreeFamilyFon
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NormChoiceFacts
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MainAltAltAltMore
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DeRhamFamilyAway
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CrysBridge
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HoldsAll

set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
namespace GlobalTheory.JumpShapeAt
open Classical
theorem main_alt_alt : Hypotheses₂ → ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (X : KillingConditions.HubData D) (C₂ : ℝ), _root_.GlobalTheory.NLink.SetupAlt L nch HW X C₂ → ∀ ep, AdmissibleParameterJ.hodgeTateJumpsAtModulesForSign D ep → ∀ i, EmbeddingTypes.admG2 i (X.r i) ep := by
  intro hPr D L P nch HW F Cm X C₂ S ep hJ i h0 h1 w hw C
  have hR : GoodR D.nd i (X.r i) := S.canon.fam.good i
  have hA := S.facts.toCore.admA
  have hg : D.nd.l i ∉ TwistedPlaces.gset D := by
    simp only [TwistedPlaces.gset, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨h0, h1⟩
  have hChi := _root_.GlobalTheory.ChiOneNoPt.main_alt_alt_alt hPr.font D hA.1 hA.2.2.2.1 hA.2.2.2.2.2.2 S.facts.block S.facts.muUnr i hg
  have hG2 := S.facts.g2.1 i (X.r i) hR
  have hcr : ∀ x, IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rO D.nd i (X.r i) x))) :=
    fun x => GlobalTheory.DualTwistCrys.crys_coef D i (X.r i) w hw C x
      (_root_.GlobalTheory.DualTwistCrys.crys_bridge_alt_alt D i (X.r i) hR hG2 h0 h1 w hw x)
  refine ⟨hcr, fun x => GlobalTheory.DualTwistCrys.tw_crys D i (X.r i) w hw C x
    (GlobalTheory.DualTwistCrys.crys_chi D i hChi w hw C) (hcr x), fun τ => ?_⟩
  obtain ⟨g, ρ, hRd, hx, -⟩ := hJ i (X.r i) hR w hw C τ
  have hAJ := S.facts.admJ L S.par
  have hJall : AdmissibleParameterJ.JumpConditions L := _root_.GlobalTheory.JumpStatement.holds_all_alt D L hAJ
  have hj := D.nd.j_range i
  have hint := jj_int D L S.par hAJ.2.2.2.1 i _ g ρ hRd (decide (AdmissibleParameterJ.TypeU D ep g))
  obtain ⟨Cl, Lo, hS⟩ := shape D L S.par hJall.2.1 hJall.2.2.1 _ hj.1 hj.2 ρ _ hint
  refine ⟨Cl, Lo, fun x => ?_⟩
  have hsg : (if EmbeddingTypes.EmbU C ep τ then (1 : ℤ) else -1) = (if decide (AdmissibleParameterJ.TypeU D ep g) then 1 else -1) := by
    by_cases hT : AdmissibleParameterJ.TypeU D ep g
    · rw [if_pos ((embU_iff D i w hw C τ ep g ρ hRd).2 hT), decide_eq_true hT]; rfl
    · rw [if_neg (mt (embU_iff D i w hw C τ ep g ρ hRd).1 hT), decide_eq_false hT]; rfl
  rw [hsg]
  convert hS using 1
  funext a
  rw [(hx x a).2.1]
end GlobalTheory.JumpShapeAt
end
