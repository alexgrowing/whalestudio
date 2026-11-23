import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeriesRealizationOfPublished
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GalSide
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExportAtOfBundlesStatement
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.IsPotCrysAtOfMono0

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published
namespace GlobalTheory.ExportClose0
theorem exportAt_bundles_alt : Cheb → PoitouTateTotallyComplex → CohDimTwo → TameLocal → LocalFiniteness → LocalTateDuality → LocalEulerChar → GlobalFiniteness → GlobalEulerChar → UnramifiedOrthogonality → BlochKatoReduction.Gen.ArchimedeanSignatureMatching → GreenbergWiles → RayCharacterArtin → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.ChebotarevDegreeOne → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.ToricDenominator → GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat → GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.SerInt → GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.HeckeInt → GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.HeckeTransform → GlobalTheory.HeckeSupSt.HeckeReadTie → ∀ (D : D7) (nch : NChoice D) (xd : ThData D) (X : RealSide D) (Y : SerSide X (twEOf xd)) (G : _root_.GlobalTheory.TwInputs.GalSideAlt D), FieldOk X → _root_.UpperTheory.GalS.GalHodgeN D G.wd → LocalSituation.Conclusion5 D → NChTie D nch → (∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → BaseTup Y (nch.twI w)) → GlobalTheory.Mem.Top.ExportAt D nch xd := by
  intro hCheb hPT hCD hTame hLF hLTD hLEC hGF hGEC hUO hadm hGW hRCA hCusp hCheb1 hGAR hTor hSR hSI hHI hHT hHRT
  intro D nch xd X Y G hF hGH hconds hTie hBase
  exact _root_.GlobalTheory.T.realization_of_published_alt hCheb hPT hCD hTame hLF hLTD hLEC hGF hGEC hUO hadm hGW hRCA hCusp hCheb1 hGAR hTor D nch xd X Y G
    (GlobalTheory.T.thetaSeries_rationality_and_coefficientBound hCusp hGAR hSR hSI D X (twEOf xd) Y hF).1
    (GlobalTheory.T.thetaSeries_rationality_and_coefficientBound hCusp hGAR hSR hSI D X (twEOf xd) Y hF).2
    (GlobalTheory.T.heckeOperator_preserves_supLattice_realSide hCusp hHI hHT hHRT D X)
    hGH hconds hF.galois hF.roots hTie hBase
end GlobalTheory.ExportClose0
end
