import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftColumnRowSetup
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BoundAtTwoThreeFamilyFon
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DeRhamFamilyAway
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NormChoiceFacts
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HoldsAll
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.UnrCrysAtRangePrime
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsFurtherTerStatement

set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
noncomputable section
namespace GlobalTheory.LiftExpSplit
open Module
variable {D : D7}
end GlobalTheory.LiftExpSplit
end
namespace GlobalTheory.LiftExpSplit
theorem main_alt_alt : Hypotheses₂ → ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (X : KillingConditions.HubData D) (C₂ : ℝ), _root_.GlobalTheory.NLink.SetupAlt L nch HW X C₂ → ∀ i, TwistedPlaces.TwLoc D i → D.nd.l i ∉ TwistedPlaces.gset D → KillingConditions.RangeAD L X.exc (D.nd.l i) → TwistedPlaces.SplitK D (D.nd.l i) → EmbeddingTypes.LiftExponentColumn i (X.r i) (X.dc i) (X.eS i) ∧ EmbeddingTypes.LiftExponentDualPlaces i (X.r i) (X.dc i) (X.eS i) := by
  intro hP D L P nch HW F Cm X C₂ hS i hTw hg hR hsp
  have hAJ : _root_.Formalism.MainNotions.AdmissibleParameterJ.AdmJAlt L := hS.facts.admJ L hS.par
  have hJ : AdmissibleParameterJ.JumpConditions L := _root_.GlobalTheory.JumpStatement.holds_all_alt D L hAJ
  obtain ⟨⟨ep, hA⟩, -, -, -, he, -, -⟩ := hJ
  have hgood : ∀ i, GoodR D.nd i (X.r i) := hS.canon.fam.good
  have hAA : _root_.Formalism.MainNotions.SumRepresentations.AdmAAlt D := hS.facts.toCore.admA
  have hUC := _root_.GlobalTheory.HubX.unrCrysAtRangePrime_alt hP.font D L X hgood hAA.1 hAA.2.2.2.1 hAA.2.2.2.2.2.2
    hS.facts.g2.1 hS.facts.block hS.facts.muUnr i hTw hg hR hsp
  have hg0 : D.nd.l i ≠ D.host.g 0 := fun h => hg (by simp [TwistedPlaces.gset, h])
  have hg1 : D.nd.l i ≠ D.host.g 1 := fun h => hg (by simp [TwistedPlaces.gset, h])
  have hG2 : EmbeddingTypes.admG2 i (X.r i) ep := _root_.GlobalTheory.T.admG2_of_setup_jumps hP D L P nch HW F Cm X C₂ hS ep hA i
  have h2 : D.nd.l i ≠ 2 := fun h => hR.1 (Or.inl (h ▸ D.host.two_mem_small))
  have heS : X.eS i = eA L 23 (D.nd.l i) := hS.canon.data.eS i hsp
  have h54 : LiftingTheory.LiftTheoremAllCases D HW F 23 32 32 :=
    (GlobalTheory.T.localConstants_from_admitted_local_Galois_statements hP.bk hP.tate hP.euler D HW F Cm).2.2.2.2.2.2.2
  have hcont : TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i (X.r i) := continuous_family_of D i (X.r i) (hgood i)
  have hFont : TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL (D := D) i := GlobalTheory.T.fontaineAtPlacesOverL D i
  have hj := D.nd.j_range i
  have hhB : AdmissibleParameterJ.hJ L + 2 = Formalism.MainNotions.TwistedPlaces.hB L := by
    unfold AdmissibleParameterJ.hJ Formalism.MainNotions.TwistedPlaces.hB; ring
  have hwinT : ∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (x : D.nd.X i) τ,
      JumpsInV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i (X.r i) x))) τ
        (Set.Icc (-(Formalism.MainNotions.N.hN L : ℤ)) (Formalism.MainNotions.N.hN L)) := by
    intro w hw C x τ a ha
    obtain ⟨g, ρ, -, hx, -⟩ := hA i (X.r i) (hgood i) w hw C τ
    have hq := (hx x a).1.mp ha
    have hb := he.1 (D.nd.j i) hj.1 hj.2 ρ _ _ hq
    have hb2 := he.2.1
    apply mem_window L a
    have hc : (((a : ℚ) : ℝ)) = (a : ℝ) := by push_cast; rfl
    rw [hc] at hb
    linarith
  have hwinD : ∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (x : D.nd.X i) τ,
      JumpsInV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rDuO D.nd i (X.r i) x))) τ
        (Set.Icc (-(Formalism.MainNotions.N.hN L : ℤ)) (Formalism.MainNotions.N.hN L)) := by
    intro w hw C x τ a ha
    obtain ⟨g, ρ, -, hx, -⟩ := hA i (X.r i) (hgood i) w hw C τ
    have hq := (hx x a).2.2.1.mp ha
    have hb := he.1 (D.nd.j i) hj.1 hj.2 ρ _ _ hq
    have hb2 := he.2.1
    apply mem_window L a
    have hc : (((-(a : ℚ) - 1 : ℚ)) : ℝ) = -(a : ℝ) - 1 := by push_cast; rfl
    rw [hc] at hb
    rw [abs_le] at hb ⊢
    constructor <;> linarith [hb.1, hb.2]
  rw [heS]
  refine ⟨?_, ?_⟩
  · intro w hw _ C hC
    exact lift_of_window i w hw C hC (hUC.1 w hw) h2 (fun x => TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i (X.r i) x))
      (fun x v => locC_cont D i _ (rTwO_cont D i (X.r i) hcont x) w hw C v) (hFont w hw C)
      (Formalism.MainNotions.N.hN L) (Formalism.MainNotions.N.hN L) (fun x => (hG2 hg0 hg1 w hw C).2.1 x) (fun x => hwinT w hw C x)
      HW F (by norm_num) h54 _ (shape_le_eA L 23 (D.nd.l i))
  · intro w hw _ C hC
    exact lift_of_window i w hw C hC (hUC.1 w hw) h2 (fun x => TruncatedSeriesCountingIdentities.locC C (rDuO D.nd i (X.r i) x))
      (fun x v => locC_cont D i _ (rDuO_cont i (X.r i) hcont x) w hw C v) (hFont w hw C)
      (Formalism.MainNotions.N.hN L) (Formalism.MainNotions.N.hN L) (fun x => hUC.2 w hw C hC x) (fun x => hwinD w hw C x)
      HW F (by norm_num) h54 _ (shape_le_eA L 23 (D.nd.l i))
end GlobalTheory.LiftExpSplit
end
