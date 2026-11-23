import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisInputs
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GalSide
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Adm2OfIsTriple
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GaloisHypothesesOfIsTriple
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SatakeIdentityOfIsTriple
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SetHypOfIsTripleOfGalHodge
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.IsPotCrysAtOfMono0

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 800000
namespace GlobalTheory.TwGalInputs
theorem galois_inputs_alt : GlobalTheory.Published.ChebotarevDegreeOne → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.ToricDenominator → ∀ (D : D7) (G : _root_.GlobalTheory.TwInputs.GalSideAlt D), _root_.UpperTheory.GalS.GalHodgeN D G.wd → BlochKatoReduction.adm1 (BlochKatoReduction.bk0 D) ∧ BlochKatoReduction.adm2 D ∧ BlochKatoReduction.adm8 D ∧ AllGood D.nexp ∧ D.nexp.sig_all ∧ (∃ N0, BlochKatoReduction.adm9 D N0) ∧ BlochKatoReduction.adm10 D ∧ ∀ i, D.ntw.NonzeroIndexPlace i → BlochKatoReduction.Gen.SetHyp (BlochKatoReduction.bk0 D) i := by
  intro hC hArt hTor D G hGH
  have h2 : BlochKatoReduction.adm2 D := _root_.GlobalTheory.TripleAdm.adm2_of_isTriple_wildOne D G.triple (GlobalTheory.T.full_degree_label_forces_trivial_wild_inertia D G.wd G.lab)
  have hF : GlobalTheory.TypeLeaf.FrobDense D :=
    GlobalTheory.SplitFrobDense.frobDense D (GlobalTheory.Published.chebotarevDegreeOne_iff_cheb.1 hC)
  have hg := _root_.GlobalTheory.TripleLocal.adm1_adm8_selfDual_noJump_of_isTriple G.chr hF hGH h2 G.triple
  have hs := _root_.GlobalTheory.Triple.adm8_allGood_sig_of_isTriple D G.triple
  have hL := GlobalTheory.LamTie.isToricElt_of_isLamTie D _ D.ntw G.lam G.lamOk G.lamTie
  obtain ⟨N0, h9, h10, -⟩ := GlobalTheory.ToricAssembly.toric_properties hArt hTor D hL.1
  exact ⟨hg.1, h2, hg.2.1, hs.2.1, hs.2.2, ⟨N0, h9⟩, h10,
    _root_.GlobalTheory.SettingHypotheses.setHyp_of_isTriple_of_nonzeroIndexPlace hC D G.wd G.cf G.chr hGH h2 G.triple G.lam G.lamOk G.lamTie G.rank G.primes⟩
end GlobalTheory.TwGalInputs
end
