import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeometricLawsAllStatesStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RootsOfUnityRingLeWittIntegers
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeGeometricOfMultiplicityLowerBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
theorem GlobalTheory.HeightCounting.Up.geoLaws_at_levelB1_states : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ _ _ _ _ P x => ∀ (l : _root_.GlobalTheory.HeightCounting.Up.SecondIntermediateLevel hL x) (i : (Dof x).ntw.Tw), GlobalTheory.GeoTie.GeoLaws l.b.YS x.m.z.geo.fw ((Dof x).nth.iC i) := by
  intro hP hS hL
  have hH := _root_.GlobalTheory.T.heckeGeo_at_levelB1_states hP hS hL
  refine hH.trans (StepW.of_all fun K B f T w _ _ hw P x l i => ?_)
  have hint := (Dof x).nth.iC_int i
  refine ⟨?_, ?_, ?_, hw P x l i, ?_, ?_, ?_⟩
  · intro b j
    exact GlobalTheory.PointsDetectAlg.detects _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hint b j
  · intro b j
    exact GlobalTheory.GeoTie.supDescent_side _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hint b j
  · intro b j f
    exact l.b.ser.sup i _ b _ _ f
  · intro b j
    exact GlobalTheory.T.heckeQuotient_integral_framed_point_complete_field hS.hkInt _ _ _ _ _ _ _ _ _ _ _ x.m.z.geo.κ x.m.z.geo.v₀ x.m.z.geo.fw _ _ hint b j
  · intro j k Pl hk
    obtain ⟨hHP, -⟩ := GlobalTheory.T.isSplitHeckePrimeOffLevel_of_heckeIndexPlace _ _ x.m.z.geo.fw.laws i k Pl hk
    obtain ⟨n, hn⟩ := GlobalTheory.HeckeCount.card_hkKer_const _ _ _ _ (x.m.z.core.Q.Xo ((j : ℕ) + 1)) x.m.z.core.Q.c Pl.asIdeal
      (GlobalTheory.GeoTie.charAt Pl) k (GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.isHeckePrime_iff.2 hHP)
    exact ⟨n, fun b z => hn _ z.1⟩
  · intro j hj b
    exact l.b.ser.off i j b (fun h => hj (Finset.mem_Icc.2 h))
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geoLaws_iC_at_levelB1_of_serN : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ _ _ _ _ P x => ∀ (l : _root_.GlobalTheory.HeightCounting.Up.SecondIntermediateLevel hL x) (i : (Dof x).ntw.Tw), GlobalTheory.GeoTie.GeoLaws l.b.YS x.m.z.geo.fw ((Dof x).nth.iC i) := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.geoLaws_at_levelB1_states | exact _root_.GlobalTheory.HeightCounting.Up.geoLaws_at_levelB1_states | (intros; apply _root_.GlobalTheory.HeightCounting.Up.geoLaws_at_levelB1_states <;> assumption)
end
end
