import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CentralFrameSplitPlaceNontrivial
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
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.central_frame_split_place_nontrivial : ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AtMem hL fun _ _ _ _ w Z _ _ t _ _ c =>
  ∀ (ad : MtAd t.r.Y c.a.all.gal.mt) (i : (w.st Z).toD7.nd.Loc) s (k : Fin (w.st Z).toD7.R.m), t.r.Y.tup s = (w.st Z).toD7.nd.mu i →
    Nontrivial ((w.st Z).toD7.what₂.Mt (t.r.Y.tup s) ((k : ℕ) + 1)) →
    ∀ (s' : ReciprocityTheory.Aut.SplitPlace (w.st Z).toD7.host.E) (φ : GlobalTheory.CenFrame.Os s' →+* Formalism.L2.DIV.kP s'.w)
      (b : GL (Fin (w.st Z).toD7.R.nV) (Formalism.L2.DIV.kP s'.w)), s'.w ∈ t.r.z.R.Pg → GlobalTheory.CenFrame.IsResidue s' φ →
        GlobalTheory.CenFrame.FrameRed (GlobalTheory.FrameBlockDiagonal.rankV (w.st Z).toD7 k) (ad.PV k) (t.r.z.R.βV k) s' φ b →
        b ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 (w.st Z).toD7.R.r) := by
  first | exact @GlobalTheory.FrameBlockTriangular.blockTri_at | exact GlobalTheory.FrameBlockTriangular.blockTri_at | (intros; apply GlobalTheory.FrameBlockTriangular.blockTri_at <;> assumption)
