import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalLanglandsHypothesesOfLiteratureStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MultQ
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HypN
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocalRepresentationTheoryHypotheses
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocalLanglandsGLAndPurityAtMember
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaLocalInputs
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocalGlobalAboveEllOfCusp
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ArchimedeanLocalLanglandsCompatibility
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocalParameterStableAtUnramifiedPlace
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MultiplicityOfPrimitive
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PointwiseGaloisPropertiesOfLocalInputs
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspParameterAtMemberOfParallelCopy
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.Mem.LiteralAutomorphy
theorem GlobalTheory.MemberClose.exists_hyp_n_of_geometric_galois_compat : _root_.GlobalTheory.Mem.LiteralAutomorphy.NonEndoscopicHypothesesAlt → _root_.GlobalTheory.NRows.GeometricGaloisRepCompatibility → _root_.GlobalTheory.Mem.Top.Bl.EllipticHypothesis ∧ _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt ∧ SerN ∧ ∃ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.Mem.Top.Bl.LocalLanglandsHypothesis hL := by
  intro hN hX
  have hS := GlobalTheory.SerStdFit.seriesRat_of_seriesRatS
  obtain ⟨hLoc, hA, hCo, ⟨hToric, -, hT, -, -⟩, -⟩ := hN
  obtain ⟨hL, hPr⟩ := _root_.GlobalTheory.Mem.LiteralAutomorphy.localLanglandsGL_and_purity_at_member_alt hLoc hA
  have hRatio := GlobalTheory.ToricRatioBridge.ratioConj_of_toricRatioConjugates
    (GlobalTheory.ToricTransport.toricRatioConjugates_of_transport hT)
  obtain ⟨hkInt, hkTr, hkRead⟩ := GlobalTheory.HeckeMember.heckeInt_transform_readTie
  obtain ⟨hRS, hInt⟩ := GlobalTheory.seriesRatS_and_serInt_of_globalArtin hA.art
  have hSer : SerN := ⟨hS hRS, hInt, hkInt, hkTr, hkRead, hRatio⟩
  have hE : _root_.GlobalTheory.Mem.Top.Bl.EllipticHypothesis := by
    obtain ⟨hCheb, hDeg1, -, hTC, hCD, hTame, hAdm4, hRay⟩ :=
      GlobalTheory.twist_front_inputs (GlobalTheory.PoitouTateConj.poitouTateDuality_of_normalised hCo.pt) hCo.lf hCo.lt hCo.lfK hCo.ltK hCo.leK
        hA.art
    exact
      { e1 := hCheb, e2 := hTC, e3 := hCD, e4 := hTame, e5 := hCo.lf, e6 := hCo.lt, e7 := hCo.le, e8 := hCo.gf,
        e9 := hCo.ge, e10 := hCo.uo, e11 := hAdm4, e12 := hCo.gw, e13 := hRay, e14 := hDeg1, e15 := hToric,
        e16 := hSer.rat, e17 := hSer.int, e18 := hSer.hkInt, e19 := hSer.hkTr, e20 := hSer.hkRead,
        e21 := hPr.what₂.fin, e22 := hPr.what₂.gal, e23 := hPr.what₂.berger,
        e24 := _root_.GlobalTheory.GalOfCusp.local_global_above_ell_of_cusp_alt hPr.what₂,
        e25 := GlobalTheory.BlochKatoLocalOfHyp.blochKatoLocal_allPrimes_of_blochKato hCo.bk hCo.ltK hCo.leK }
  exact ⟨hE, hPr, hSer, hL, hPr, hSer, _root_.GlobalTheory.ArchFromLit.archimedean_local_langlands_compatibility_alt hLoc hA hL,
    _root_.GlobalTheory.HeightCounting.Up.conjDualParam_stable_of_prime_not_dividing_level_alt hPr (_root_.GlobalTheory.MtInMain.prN_sMt_alt_alt hPr) hL, _root_.GlobalTheory.HeightCounting.Up.ptSt_of_inputs_geometric_compat hPr hX hL, _root_.GlobalTheory.HeightCounting.Up.cuspParameter_at_member_alt hPr hL⟩
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.Mem.LiteralAutomorphy
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hyps_e_third_layer_ser_n_of_geometric_galois : _root_.GlobalTheory.Mem.LiteralAutomorphy.NonEndoscopicHypothesesAlt → _root_.GlobalTheory.NRows.GeometricGaloisRepCompatibility → _root_.GlobalTheory.Mem.Top.Bl.EllipticHypothesis ∧ _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt ∧ SerN ∧ ∃ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.Mem.Top.Bl.LocalLanglandsHypothesis hL := by
  first | exact @_root_.GlobalTheory.MemberClose.exists_hyp_n_of_geometric_galois_compat | exact _root_.GlobalTheory.MemberClose.exists_hyp_n_of_geometric_galois_compat | (intros; apply _root_.GlobalTheory.MemberClose.exists_hyp_n_of_geometric_galois_compat <;> assumption)
end
end
