import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RealizationOfPublished
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GalSide
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.InputsOfSidesStatement
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.IsPotCrysAtOfMono0

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published
namespace GlobalTheory.ExportClose
open Classical in
theorem exportAt_of_bundles_alt : Cheb → PoitouTateTotallyComplex → CohDimTwo → TameLocal → LocalFiniteness → LocalTateDuality → LocalEulerChar → GlobalFiniteness → GlobalEulerChar → UnramifiedOrthogonality → BlochKatoReduction.Gen.ArchimedeanSignatureMatching → GreenbergWiles → RayCharacterArtin → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.ChebotarevDegreeOne → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.ToricDenominator → ∀ (D : D7) (nch : NChoice D) (xd : ThData D) (X : RealSide D) (Y : SerSide X (twEOf xd)) (G : _root_.GlobalTheory.TwInputs.GalSideAlt D), (∀ i, D.ntw.NonzeroIndexPlace i → ∀ j b, RatRow Y.YS X.geo.v₀ Y.Z.good i j b) → XiBdd Y.Z.rd → (∀ j, GlobalTheory.IndefiniteRowSideFullHecke.LatticesOverBalls.HkSupAt X.core X.R.toRealDat j) → _root_.UpperTheory.GalS.GalHodgeN D G.wd → LocalSituation.Conclusion5 D → IsGalois ℚ ↥D.LL0 → (∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (Formalism.L2.Host.embLL0 D).fieldRange) → NChTie D nch → (∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → BaseTup Y (nch.twI w)) → GlobalTheory.Mem.Top.ExportAt D nch xd := by
  intro hCh hPT hCD hTL hLF hLT hLE hGF hGE hUO h4 hGW hRC hDec hCh1 hArt hTor D nch xd X Y G hRat hXi hHk hHodge h5 hGal hRoots hTie hBase
  obtain ⟨N0, hI⟩ := _root_.GlobalTheory.T.exists_inputs_of_galHodgeN_roots hCh1 hArt hTor D X (twEOf xd) Y G hRat hXi hHk hHodge hRoots
  have hW : ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → D.ntw.NonzeroIndexPlace (nch.twI w) :=
    GlobalTheory.Mem.Top.twistedPlaceIndex_mem_firstPair_of_compatibleChoice D nch hTie hGal
  let S : ∀ (i : D.ntw.Tw) (j : ℕ) (b : Bool), Finset (D.nexp.Dat i j b) := fun i j b =>
    if h : D.ntw.NonzeroIndexPlace i ∧ j ∈ Finset.Icc 1 D.R.m then
      Classical.choose (GlobalTheory.T.exists_basis_averaged_series_of_class_sums D (twEOf xd) hI.t4 i h.1 j h.2 b) else ∅
  refine ⟨N0, S, fun i hi => ?_, fun w hw => ⟨hI.hyp _ (hW w hw), ?_, ?_⟩⟩
  · exact GlobalTheory.TwExportTop.twistAllPowers_of_galoisCohomology_classField hCh hPT hCD hTL hLF hLT hLE hGF hGE hUO h4 hGW hRC D (twEOf xd) N0 h5
      hI.a1 hI.a2 hI.a8 hI.good hI.sig hI.a9 hI.a10 hI.univChar hI.off hI.rel hI.l3 hI.t4 hI.type hI.univ hI.supG
      hI.supFull hI.supHk hI.commG hI.comm hI.ss i hi
  · intro j hj b
    exact GlobalTheory.T.fullRank_thetaSeries_forms_of_rational_scalars hDec D X (twEOf xd) Y (nch.twI w) (hBase w hw) (hRat _ (hW w hw)) j hj b
  · intro j hj b
    have h : D.ntw.NonzeroIndexPlace (nch.twI w) ∧ j ∈ Finset.Icc 1 D.R.m := ⟨hW w hw, hj⟩
    show IntegralHeckeForms.BasisOf D.nexp (nch.twI w) j b (IntegralHeckeForms.SgJ D.nexp (twEOf xd) (nch.twI w) j b) (S (nch.twI w) j b)
    simp only [S, dif_pos h]
    exact Classical.choose_spec (GlobalTheory.T.exists_basis_averaged_series_of_class_sums D (twEOf xd) hI.t4 _ h.1 j h.2 b)
end GlobalTheory.ExportClose
end
