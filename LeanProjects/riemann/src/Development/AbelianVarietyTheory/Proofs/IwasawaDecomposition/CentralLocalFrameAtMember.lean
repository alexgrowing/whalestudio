import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroWild
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAboveL
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsXdAllIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JumpsCardOfBuilt
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CenterEqSum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCompOfOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBlockDiagonalWithIdentity
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelFinEMemDivisorStandardStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CentralFrameSplitPlaceNontrivialStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.G0LiftUnitaryCentralFrameStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjParahoricBlockLiftStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev

namespace GlobalTheory.CenLocAt

set_option maxHeartbeats 4000000 in

theorem frameAt_of_layer : ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AtMem hL fun _ _ _ _ w Z _ _ t _ _ c => ∀ (ad : MtAd t.r.Y c.a.all.gal.mt) (i : (w.st Z).toD7.nd.Loc) s k, t.r.Y.tup s = (w.st Z).toD7.nd.mu i → GlobalTheory.CenLocAt.FrameAt t.r.Y t.r.z.cG k (ad.PV k) s := by
  intro hL
  refine GlobalTheory.HeightCounting.Up.Model.AtMem.imp
    (GlobalTheory.HeightCounting.Up.Model.AtMem.and (GlobalTheory.HeightCounting.Up.Model.AtMem.and (GlobalTheory.T.level_finE_mem_divisor_standard hL) (GlobalTheory.T.central_frame_split_place_nontrivial hL)) (GlobalTheory.T.g0_lift_unitary_central_frame hL)) ?_
  intro K B f T w Z Wt p0 t nch n c h ad i s k hs
  obtain ⟨⟨hA, hB⟩, hC⟩ := h
  obtain ⟨L, hL1, hU, hLc⟩ := hC s
  obtain ⟨hSt, hFR⟩ := hA ad k s
  refine ⟨L, hL1, fun hN => ?_⟩
  refine GlobalTheory.T.exists_conj_parahoric_block_lift t.r.z.R t.r.z.cG k s (ad.PV k) L hU hSt (fun PP hPP => ?_) hLc
  obtain ⟨s', φ, b, hw, hres, hfr⟩ := hFR PP hPP
  exact ⟨s', φ, b, hw, hres, hfr, fun hP => hB ad i s k hs hN s' φ b (hw ▸ hP) hres hfr⟩

end GlobalTheory.CenLocAt
