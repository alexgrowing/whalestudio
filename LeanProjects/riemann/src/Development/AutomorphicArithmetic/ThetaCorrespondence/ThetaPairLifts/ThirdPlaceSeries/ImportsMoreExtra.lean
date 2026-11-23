import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitBoundOfParams
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DeRhamFamilyAway
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HoldsAllStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.JointConditionsRangeBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HubXTypePrimeConditions
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RestPtAtQD
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MainAltAltMoreStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.JointCondH0WallOfCanon
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RestPtOfPtFam
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.UnrCrysAtRangePrime
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AmbAllGoodPointsStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.JointCondH0allCanon
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.TrivialLocalCondition

set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
namespace GlobalTheory.HubX.Assembly
theorem main_alt_alt : GlobalTheory.Published.FontaineBcris → Formalism.GaloisCohomology.LocalFinitenessK → GlobalTheory.TwSys.Cheb → ∀ (D : D7) (L : SizeData₂ D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (R : KillingConditions.RowK) (C : NChoice D) (X : KillingConditions.HubData D) (c : ℝ) (CT : ℕ), GlobalTheory.HubX.Canon L HW R X → ParameterChoice' D L → 1 ≤ L.sc.L → 120 ≤ c → (CT : ℝ) ≤ L.sc.b → _root_.Formalism.MainNotions.AdmissibleParameterJ.AdmJAlt L → EmbeddingTypeJumps.ParametersPolynomiallyBounded L → _root_.Formalism.MainNotions.SumRepresentations.AdmAAlt D → _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → SumRepresentations.Conclusion42 D → SumRepresentations.ConclusionG5 D → SumRepresentations.ConclusionZ D → ResidualIrreducibleRankR D → GlobalTheory.SplitCoef.OSplit D → GlobalTheory.CoefDuty.TakenAll D → NChTie D C → GlobalTheory.PtCore.TriplesGood D → GlobalTheory.PtCore.SameTwist D C → GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.BlockCharParam D → GlobalTheory.HubX.MuUnr D → GlobalTheory.HubX.DepthZeroG D → (∀ i, GoodR D.nd i (X.r i)) ∧ (∀ i, EmbeddingTypeJumps.AtQD i → ∀ π ∈ D.nd.Zgood i, RestPt i (X.r i) (X.ρ i) π) ∧ EmbeddingTypeJumps.FontaineSubOfSumsAtDistinguishedPrimes X.r X.ρ ∧ KillingConditions.DataAD L HW X R ∧ GlobalTheory.HubX.CondCB L X c ∧ KillingConditions.ConstantColumnBound L X c ∧ (∃ M0 h0 : ℕ, GlobalTheory.HubX.JointCond_H0Wall D HW F X M0 h0) ∧ (∀ i, D.nd.l i ∉ TwistedPlaces.gset D → ∀ π ∈ D.nd.Zgood i, RestPt i (X.r i) (X.ρ i) π) ∧ (∀ i, KillingConditions.RangeAD L X.exc (D.nd.l i) → ∀ π, ∃ M0 h0 : ℕ, JointConditionTameBound D HW F i (X.r i) π M0 h0 (X.cB i)) ∧ (∀ i : D.nd.Loc, TwistedPlaces.TwLoc D i → D.nd.l i ∉ TwistedPlaces.gset D → KillingConditions.RangeAD L X.exc (D.nd.l i) → TwistedPlaces.SplitK D (D.nd.l i) → (∀ hJ : AdmissibleParameterJ.ConclusionJa D, EmbeddingTypes.hypDecl i (X.dc i) (Exists.choose hJ)) ∧ (∀ v ∈ placesOver D.host.E (D.nd.l i), v.asIdeal.ramificationIdx ℤ = 1) ∧ (∀ ep, EmbeddingTypes.ambTypeD (D := D) i ep) ∧ (∀ π ∈ D.nd.Zgood i, EmbeddingTypes.UnramifiedTrivialH1f (D := D) i (X.dc i) ∧ EmbeddingTypes.ambDual (D := D) i (X.ρ i) π (X.dc i) ∧ EmbeddingTypes.ambT2 (D := D) i (X.ρ i) π (X.dc i) ∧ EmbeddingTypes.ambW (D := D) i (X.ρ i) π (X.dc i) ∧ EmbeddingTypes.ambFil (D := D) i (X.r i) (X.ρ i) π (X.dc i) ∧ EmbeddingTypes.H1fFiniteRankTorsion (D := D) i (X.ρ i) π (X.dc i) ∧ LargeLevelLemmas.adm51 (D := D) i (X.r i) (X.ρ i) π ∧ ∃ M0 h0 : ℕ, GlobalTheory.HubX.DecompositionInvariantsCondition D HW i (X.ρ i) π (X.dc i) (X.c0 i) M0 h0) ∧ (∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), (D.nbr i w hw).Kw.1 ≤ Loc.MaximalUnramifiedExtension (D.nd.l i)) ∧ ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (Ce : TruncatedSeriesCountingIdentities.CoefExt D i w hw), Ce.IsGood → ∀ x : D.nd.X i, IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC Ce (rDuO D.nd i (X.r i) x)))) ∧ KillingConditions.SignatureChoiceCondition X.ρ C ∧ (∀ (i : D.nd.Loc) (k : Fin 2), TwistedPlaces.TwLoc D i → D.nd.l i = D.host.g k → HG D.nd D.naut i → GoodR D.nd i (X.r i) ∧ (∀ π ∈ D.nd.Z i, IsRhoOf D.nd i π (X.ρ i π) ∧ IsSSRep (rhoChiK D i (X.ρ i π))) ∧ ∃ (s S : ℕ) (sg : HeightOneSpectrum (𝓞 D.host.E) → Bool) (U : HeightOneSpectrum (𝓞 D.host.E) → Finset ℤ), X.eta + D.R.t + 1 < s ∧ CT * ((s + S) * (D.R.nV + 1) ^ 2 + (D.R.nV + 1) ^ 3) < D.host.g k ∧ PairedCharacterCondition.SignOK i sg ∧ PairedCharacterCondition.HostJ i (X.r i) X.eta s S sg U) ∧ (X.eta : ℝ) ≤ 2 * L.etaSz := by
  intro hFB hLF hCh D L HW F R C X c CT hX hPm hL hc hCT hAJ hAP hAA h41 h42 hG5 hZ hRB hOS hTA hNT hTG hST hBC hMU hDZ
  have hJ : AdmissibleParameterJ.JumpConditions L := _root_.GlobalTheory.T.jump_closed_forall_d7 D L hAJ
  have hG2 : _root_.Formalism.MainNotions.AdmissibleParameterJ.DeRhamFamilyAwayAlt D := hAJ.1
  have htie : SumRepresentations.tie0 D := hAA.1
  have had1 : SumRepresentations.adm1 D := hAA.2.2.1
  have had2 : _root_.Formalism.MainNotions.SumRepresentations.adm2_alt D := hAA.2.2.2.1
  have had5 : SumRepresentations.adm5 D := hAA.2.2.2.2.2.2
  have hFont : ∀ i, TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL (D := D) i := GlobalTheory.T.fontaineAtPlacesOverL D
  have hfam : GlobalTheory.PtCore.PtFam D X.r X.ρ := hX.fam
  have hcB : ∀ i, GlobalTheory.HubLoc.cBnum (D.nd.l i) ⌊2 * L.sc.b⌋₊ D.R.t (4 * D.R.n * D.R.nV) ≤ X.cB i := by
    intro i; rw [hX.cB]; exact le_rfl
  have hCl := _root_.GlobalTheory.T.joint_conditions_range_bound_alt hFB hLF D HW F L X (fun L' h => _root_.GlobalTheory.T.jump_closed_forall_d7 D L' h) hAJ hAP h41 hOS hfam hcB
  have hRes : GlobalTheory.PtCore.ResAbsIrr D := GlobalTheory.PtCore.residualAbsIrredGoodPoint_of_residualIrred D hRB
  have hGPR : GlobalTheory.PtCore.GoodPtRow D := GlobalTheory.Proof.LocalGlobalAssembly.main D htie h42 hZ
  have hLgc : _root_.UpperTheory.GalS.NoCondition D := _root_.UpperTheory.GalS.noLgc_alt D htie had1 had2 had5
  have hCC := GlobalTheory.HubX.blockAndTorsionExponentBounds_canonicalHubData D L HW R X hX hL c hc
  have hTP := _root_.UpperTheory.GalS.hubX_typePrime_conditions_alt D L HW R X hX hPm hJ hAP hG5 hLgc hDZ CT hCT
  refine ⟨hfam.good, _root_.GlobalTheory.restPt_atQD_alt hFB D X.r X.ρ hfam h41 hOS,
    _root_.GlobalTheory.T.fontaine_quotient_degrees_of_ptFam hFB D L hG2 hJ.1 X.r X.ρ hfam, hX.data, hCC.1, hCC.2,
    _root_.GlobalTheory.HubX.jointCond_H0Wall_of_canon_alt hFB D L HW R X hX F hJ h41 hFont,
    _root_.GlobalTheory.restPt_of_ptFam_aux41_oSplit hFB D X.r X.ρ hfam h41 hOS, hCl.2.1, ?_,
    GlobalTheory.JointSix.main hCh D C X.r X.ρ hfam hNT hTG hST hGPR hRes, hTP.1, hTP.2⟩
  intro i hTw hg hr hs
  have hsp := GlobalTheory.HubX.SplitDecl.splitRowPrime_of (L := L) (X := X) i hg hr hs
  have hUC := _root_.GlobalTheory.HubX.unrCrysAtRangePrime_alt hFB D L X hfam.good htie had2 had5 hG2 hBC hMU i hTw hg hr hs
  refine ⟨fun hJa => (GlobalTheory.HubX.SplitDecl.main D L HW R X hX hJa i hTw hg hr hs).1,
    (GlobalTheory.HubX.SplitDecl.main D L HW R X hX hJ.1 i hTw hg hr hs).2,
    fun ep => GlobalTheory.T.ambientType_conjugatePlace_at_splitPrime D i ep hsp, ?_, hUC.1, hUC.2⟩
  intro π hπ
  have h78 := _root_.GlobalTheory.T.ambT2_of_deRham_family hFB D L X hG2 hJ.1 hJ.2.2.1 hfam i hg π hπ
  exact ⟨GlobalTheory.T.unramifiedTrivialH1f_of_decl D i (X.dc i), hCl.2.2.1 i hg π hπ, h78.1, h78.2.1, h78.2.2.1, hCl.2.2.2 i π,
    GlobalTheory.T.admissibleAtGoodPoints_of_coefRing_taken_at_live hCh D X hTA hRes hfam i π hπ,
    _root_.GlobalTheory.HubX.jointCondH0all_canon_alt hFB D L HW R X hX hJ h41 hFont i hTw hg hr hs π hπ⟩
end GlobalTheory.HubX.Assembly
end
