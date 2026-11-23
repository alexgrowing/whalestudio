import Development.AutomorphicArithmetic.ResidueCharacters.ConclusionSplitOfHub
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BoundAtTwoThreeFamilyFon
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NormChoiceFacts
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DeRhamFamilyAway
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HoldsAll
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SetPointGood
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsFurtherTerStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RestPtOfStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MainAltAltBisStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AmbAllGoodPointsStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ClosingFamilyX

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
namespace UpperTheory.N
theorem conclusion_split_alt (Pr : Hypotheses₂) (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (X : KillingConditions.HubData D) (C₂ : ℝ) (S : _root_.GlobalTheory.NLink.SetupAlt L nch HW X C₂)
    (i : D.nd.Loc) (hg : D.nd.l i ∉ TwistedPlaces.gset D) (N : ℕ) (hC : CycAt N i) (hL : EmbeddingTypes.hypL i)
    (hdecl : ∀ ep, (∃ dc : TruncatedSeriesCountingIdentities.Decl D i, EmbeddingTypes.hypDecl i dc ep) ∧ EmbeddingTypes.ambTypeD (D := D) i ep)
    (hK : LiftK (D.loc (D.nd.l i)) ∧ InvariantsKilledOverCyclotomic (D.loc (D.nd.l i)) ∧ TBK (D.loc (D.nd.l i))) :
    ∃ dc : TruncatedSeriesCountingIdentities.Decl D i, EmbeddingTypes.RowsAreConj i dc ∧ ∀ π ∈ D.nd.Zgood i,
      EmbeddingTypes.ShaBoundTheoremB i (X.ρ i) π dc (eL (D.nd.l i) N (Formalism.MainNotions.N.hN L))
        (fun _ => c0L (D.nd.l i) N (GlobalTheory.HubX.hOf L) (4 * D.R.n * D.R.nV))
        (cBL (D.nd.l i) N ⌊2 * L.sc.b⌋₊ (4 * D.R.n * D.R.nV) D.R.t) ∧
      (∀ u ∈ dc.col, (Br.h0W i u (X.ρ i) π : ℝ) ≤
        (D.R.r : ℝ) * (c0L (D.nd.l i) N (GlobalTheory.HubX.hOf L) (4 * D.R.n * D.R.nV) : ℕ)) ∧
      ∀ v ∈ D.nd.Q i, D.nd.zeta i v ≠ 1 := by
  have fa := S.facts
  have hAJ : _root_.Formalism.MainNotions.AdmissibleParameterJ.AdmJAlt L := fa.admJ L S.par
  have hJ : AdmissibleParameterJ.JumpConditions L := _root_.GlobalTheory.JumpStatement.holds_all_alt D L hAJ
  have hJ' := hJ
  obtain ⟨⟨ep, hep⟩, hJb, hJc, -, hJe, hJf, -⟩ := hJ'
  have hfam := S.canon.fam
  have hg0 : D.nd.l i ≠ D.host.g 0 := hL.2.2.2.1
  have hg1 : D.nd.l i ≠ D.host.g 1 := hL.2.2.2.2
  obtain ⟨⟨dc, hdc⟩, hType⟩ := hdecl ep
  refine ⟨dc, hdc.2, fun π hπ => ?_⟩
  have hZ : π ∈ D.nd.Z i := LargeLevelLemmas.zgoodSubsetZ i hπ
  have sp := _root_.GlobalTheory.T.set_pt_of_setup_not_twisted Pr D L P nch HW F Cm X C₂ S i hg π hπ
  have hρ := hfam.cont i π
  obtain ⟨sub, acont, a56⟩ := amb_of_setPt i X π dc sp hρ
  obtain ⟨g1, g2, g3, g4, _, g5x, g6, bk, cont, ss, dec, eps, tie, shape, font, hH2, cft⟩ := sp
  have hG2 := _root_.GlobalTheory.T.admG2_of_setup_jumps Pr D L P nch HW F Cm X C₂ S ep hep i
  have hG5 := _root_.GlobalTheory.T.admG5_of_setup Pr D L P nch HW F Cm X C₂ S i hg π hπ
  have hcr := _root_.GlobalTheory.T.decomposition_fontaine_at_places_over_l D i (X.r i) (X.ρ i) π fa.Conclusion1.1 font (hfam.good i) hρ dec hg0 hg1
  have hjp := GlobalTheory.T.decomposition_local_above D L ep hep hJb hJc hJe hJf i (X.r i) (X.ρ i) π (hfam.good i) hZ dec
  have hW : JumpsNoZero i (WpO D.nd i (X.ρ i) π) (GlobalTheory.HubX.hOf L) :=
    fun w hw C => ⟨(hcr w hw C).2.2.1, fun τ => hjp w hw C τ _ (Or.inl rfl)⟩
  have hT2 : JumpsNoZero i (T2O D.nd i (X.ρ i) π) (GlobalTheory.HubX.hOf L) :=
    fun w hw C => ⟨(hcr w hw C).2.2.2, fun τ => hjp w hw C τ _ (Or.inr rfl)⟩
  obtain ⟨lc, lr⟩ := lift_exponent_admissible_cols_rows_of_crystalline L i N hK.1 hC X dc hfam.good ep hep hJe font
    (fun w hw C x => (hG2 hg0 hg1 w hw C).2.1 x) (fun w hw C x => (hcr w hw C).2.1 x)
  have hH0 := invariants_length_admissible_of_nonzero_jumps i N hK.2.1 hC (X.ρ i) π dc _ hρ hT2
  obtain ⟨ht, hWin⟩ := GlobalTheory.T.hodgeTateJumpWindow_of_jumpSets D L hJ S.par67
  have tb9 := block_condition_at_places_of_jump_window i N hK.2.2 hC (X.r i) π _ ht (hWin i (X.r i) (hfam.good i) π)
  have tb : EmbeddingTypes.admTB i (X.r i) π dc _ := fun w hw _ C hC' => tb9 w hw C hC'
  obtain ⟨l51, l52, _⟩ := GlobalTheory.charpoly_span_and_hom_relations_of_admissible D i (X.r i) (X.ρ i) π g1
  have h78 := _root_.GlobalTheory.T.ambT2_of_deRham_family Pr.font D L (withDc X i dc) fa.g2.1 hJ.1 hJc hfam i hg π hπ
  rw [withDc_dc] at h78
  have hcB : ∀ k, GlobalTheory.HubLoc.cBnum (D.nd.l k) ⌊2 * L.sc.b⌋₊ D.R.t (4 * D.R.n * D.R.nV) ≤ (withDc X i dc).cB k := by
    intro k
    show _ ≤ X.cB k
    rw [S.canon.cB]; exact le_rfl
  have hCl := _root_.GlobalTheory.closingFamilyX_alt_alt Pr.font Pr.fin D HW F L (withDc X i dc)
    (fun L' h => _root_.GlobalTheory.JumpStatement.holds_all_alt D L' h) hAJ S.par67 fa.Conclusion1.1 fa.large.2.1 hfam hcB
  have dual := hCl.2.2.1 i hg π hπ
  have h1f := hCl.2.2.2 i π
  rw [withDc_dc] at dual h1f
  have a51 := GlobalTheory.T.admissibleAtGoodPoints_of_coefRing_taken_at_live GlobalTheory.Published.cheb_holds D X fa.large.2.2 (GlobalTheory.PtCore.residualAbsIrredGoodPoint_of_residualIrred D fa.rhoBar) hfam i π hπ
  have bka : LargeLevelLemmas.BlochKatoAnnihilators i := GlobalTheory.T.blochKatoAnnihilator_all_of_tateDuality_eulerChar Pr.bk Pr.tate Pr.euler D i
  have fin : LargeLevelLemmas.tateH1FinitenessAtPlacesOver i := GlobalTheory.T.tateFinitenessAll_of_localTateDuality Pr.tate D i
  have hA : EmbeddingTypes.admitted i (X.r i) (X.ρ i) π dc ep _ _ _ :=
    ⟨g1, hG2, g3, g4, hG5, g5x, g6, a56, a51, l51, l52, ⟨bk, bka⟩, lc, lr, hH0, tb, GlobalTheory.T.unramifiedTrivialH1f_of_decl D i dc, cont, ss, dec, eps,
      tie, shape, font, hH2, fin, cft, h78.2.2.2, dual, h78.1, h78.2.1, h78.2.2.1, h1f, sub, acont, hType⟩
  obtain ⟨-, -, hB⟩ := GlobalTheory.T.splitCase_bound_at_point_of_admitted_items_alt Pr.artin Pr.tate Pr.euler D i (X.r i) (X.ρ i) π dc ep _ _ _ hA (fun _ _ _ => g2) hL hdc hZ
  exact ⟨hB, fun u hu => length_invariants_Wprime_divisible_le_of_nonzero_jumps i N hK.2.1 hC (X.ρ i) π _ (GlobalTheory.NLink.AmbSub.WpO_cont i (X.ρ i) π hρ) hW u
    ((dc.cover u).1 (Or.inr hu)), fun v hv => (g5x v (Or.inr hv)).2.2.1 hv⟩
end UpperTheory.N
end
end
