import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CarriedThTw
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SettingsFormsExistList
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PlaceModelImp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DofOTw
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyPtsOfReading
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Detects
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormSumLeOfLe
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeUnitOfExportTie
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeQuotientIntegralFramedPointCompleteFieldStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyTransferEquiv
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitHeckePrimeOffLevelOfHeckeIndexPlaceStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeGeometricAllStatesStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

theorem GlobalTheory.HeightCounting.Up.geometric_laws_of_lb1 : PrN → SerN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AllSt fun _ _ _ _ _ P x => ∀ (l : SeriesLevel hL x) (i : (Dof x).ntw.Tw), GlobalTheory.GeoTie.GeoLaws l.b.YS x.m.z.geo.fw ((Dof x).nth.iC i) := by
  intro hP hS hL
  have hH := GlobalTheory.T.hecke_geometric_all_states hP hS hL
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
