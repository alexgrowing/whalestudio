import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlocksUnique
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WdOfMono0L
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CGTrue
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CMTypeEmbeddings
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuationFixedLattice
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GaloisRepOfPolarizedCuspidal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChebotarevDegreeOneIffCheb
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EigenCompatibleOfBadSet
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EsymmMapMulConst
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProdXSubCScaleMemLifts
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GalPolLiftsOfSplit
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SCuspRows

theorem allSt_and' {p q : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (P : Pre2 K w), St P → Prop}
    (h1 : AllSt p) (h2 : AllSt q) : AllSt fun K B f T w P x => p K B f T w P x ∧ q K B f T w P x :=
  EvG.imp (Step.and h1 h2) fun _ _ _ _ _ H => H.imp fun _ _ _ _ G a b c w hw P x => ⟨(G a b c).1 w hw P x, (G a b c).2 w hw P x⟩

theorem allSt_mono' {p q : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (P : Pre2 K w), St P → Prop}
    (h : AllSt p) (hq : ∀ K B f T w P x, p K B f T w P x → q K B f T w P x) : AllSt q :=
  EvG.imp h fun _ _ _ _ _ H => H.imp fun _ _ _ _ G a b c w hw P x => hq _ _ _ _ _ _ _ (G a b c w hw P x)

set_option maxHeartbeats 1000000 in

theorem exists_eigTrue {hL : GlobalTheory.Published.LocalLanglandsGL} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T}
    {P : Pre2 K w} {x : St P} (l : LA hL x) (n : InRat x.r.Y x.m.z.cG) :
    ∃ Sb, GlobalTheory.TwInputs.EigTrue (Dof x) (cfOf x) l.a.A.row Sb n.In.eig := by
  obtain ⟨Sb, h1, h2, -⟩ := GlobalTheory.TwInputs.Eig.exists_low (ι := Empty) n.In.Sb (fun i => i.elim) (fun i => i.elim) fun i => i.elim
  have h := GlobalTheory.TwInputs.Eig.eigTrue hL x.r.Y x.m.z.lev.is l.a.A.wdT l.a.A.row l.a.row n.rat.eig h1 h2
  have hC : x.m.z.R.C = cfOf x := x.m.z.lev.C
  exact ⟨Sb, (congrArg (fun c : CharFrame (Dof x) => GlobalTheory.TwInputs.EigTrue (Dof x) c l.a.A.row Sb n.In.eig) hC).mp h⟩

theorem sCusp_of_parSt : PrN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, ParSt hL → SRat hL → SCusp hL := by
  intro hP hL hPar hRat
  refine allSt_mono' (allSt_and' (allSt_and' hPar hRat) (valLL0_allSt hP)) ?_
  rintro K B f T w P x ⟨⟨hp, he⟩, hv⟩ l j hj1 hj2 σ hσ hg
  obtain ⟨π, hc, hr, hs, -, -, -⟩ := hp l j hj1 hj2 σ hσ hg
  obtain ⟨n⟩ := he l
  obtain ⟨Sb, hn⟩ := exists_eigTrue l n
  refine ⟨π, hc, hr, hs, ?_⟩
  have h2 := GlobalTheory.CuspFrobSplit.galPol_lifts_ae (Dof x) (cfOf x) l.a.A.row Sb n.In.eig hv hn j hj1 hj2 σ hσ hg π hc hs
  have h4 := GlobalTheory.GalAllPlaces.galPol_lifts_of_split hL hP.what₂.fin hP.what₂.gal hP.what₂.cheb (Dof x) l.a.A.wdT l.a.cg _ (embLL0 (Dof x)) π hc hr h2
  exact (GlobalTheory.TwistLift.galPol_lifts_tw_etaTinv (Dof x) (cfOf x) l.a.A.chr hv π h4).mono fun w hw => (Polynomial.mem_lifts _).1 hw

end GlobalTheory.SCuspRows
