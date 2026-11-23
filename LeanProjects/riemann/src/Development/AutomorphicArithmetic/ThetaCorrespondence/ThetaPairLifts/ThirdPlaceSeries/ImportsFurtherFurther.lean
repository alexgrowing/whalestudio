import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmH0Setup
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BoundAtTwoThreeFamilyFon
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HoldsAll
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NormChoiceFacts
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.JointCondH0allCanon
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified

set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
namespace GlobalTheory.NLink.PowerSmulVanishing
set_option maxHeartbeats 1600000 in
theorem main_alt_alt : Hypotheses₂ → ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (X : KillingConditions.HubData D) (C₂ : ℝ), _root_.GlobalTheory.NLink.SetupAlt L nch HW X C₂ → ∀ i, TwistedPlaces.TwLoc D i → D.nd.l i ∉ TwistedPlaces.gset D → KillingConditions.RangeAD L X.exc (D.nd.l i) → TwistedPlaces.SplitK D (D.nd.l i) → ∀ π ∈ D.nd.Zgood i, EmbeddingTypes.H0ColumnLengthBound i (X.ρ i) π (X.dc i) (X.c0 i) := by
  intro hP D L P nch HW F Cm X C₂ hS i hTw hg hRA hSp π hπ
  have hJ : AdmissibleParameterJ.JumpConditions L := _root_.GlobalTheory.JumpStatement.holds_all_alt D L (hS.facts.admJ L hS.par)
  obtain ⟨M0, h0, hl2, hJC⟩ := _root_.GlobalTheory.HubX.jointCondH0all_canon_alt hP.font D L HW (rowC C₂) X hS.canon hJ
    hS.facts.Conclusion1.1 (GlobalTheory.FontaineAdm.fontaineProperties_all_places D) i hTw hg hRA hSp π hπ
  have hlq : D.nd.l i ≠ D.host.q := fun h => hRA.2.1 (Or.inl h)
  have hld : D.nd.l i ≠ D.host.d := fun h => hRA.2.1 (Or.inr h)
  intro _ u hu w hw hconj C hC L2 hstd
  obtain ⟨-, hall⟩ := hJC u hu w hw hconj
  have hur : (D.nbr i w hw).Kw.1 ≤ MaximalUnramifiedExtension (D.nd.l i) := GlobalTheory.HubLoc.kw_le_Kur_all D i (fun h => hRA.1 (Or.inl h)) hlq hld w hw
  have hg1 : Good (D.nbr i w hw).Kw 1 C.LL := hC.good_one hl2 (le_trans (le_inf le_rfl hur) le_sup_left)
  have hT2c : Continuous fun g => T2O D.nd i (X.ρ i) π g :=
    GlobalTheory.HTW.RecS.Model.continuous_twistedDual_rhoO i (X.ρ i) π (hS.canon.fam.cont i π)
  have hc : ∀ v, Continuous fun g => matRep (Formalism.MainNotions.TruncatedSeriesCountingIdentities.locC C (T2O D.nd i (X.ρ i) π)) g v :=
    fun v => (GlobalTheory.CrysChiOne.locC_cont' C _ hT2c).matrix_mulVec continuous_const
  obtain ⟨hcr, hwin, hnj, hc0⟩ := hall C hg1 hc L2
  have hW := GlobalTheory.T.crystallineLatticeWachModuleExists_proof D HW F Cm (D.nd.l i) (D.nbr i w hw).Kw 1 C.LL hg1 (GlobalTheory.HubX.tTwoLocalLattice D i (X.ρ i) π C hc L2) M0 h0 hcr hwin
  have hkill := GlobalTheory.T.torsion_exponent_kills_invariants_of_good hP.bk hP.tate hP.euler D HW F Cm (D.nd.l i) (D.nbr i w hw).Kw 1 C.LL hg1 M0 h0
    (GlobalTheory.HubX.tTwoLocalLattice D i (X.ρ i) π C hc L2) hW hnj
  unfold EmbeddingTypes.lenInvD
  haveI : IsDiscreteValuationRing ↥(OL C.LL) := Formalism.BasicNotions.Examples₂.LB.OL_dvr C.LL
  haveI : IsFractionRing ↥(OL C.LL) ↥C.LL.1 := Formalism.BasicNotions.Examples₂.LB.OL_frac C.LL
  refine EmbeddingTypes.len_le_of_kill (Br.PD D.loc D.nbr i w hw) L2.T hstd _ (X.c0 i u) ?_
  intro x hx
  exact pow_smul_eq_zero_of_le _ hc0 (hkill x fun g => hx g)
end GlobalTheory.NLink.PowerSmulVanishing
end
