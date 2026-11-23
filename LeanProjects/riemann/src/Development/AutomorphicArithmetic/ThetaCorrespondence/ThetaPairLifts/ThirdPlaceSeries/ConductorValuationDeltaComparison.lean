import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsHeckeOfSideReadCellStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RootsOfUnityRingLeWittIntegers
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaLocalInputs
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)
namespace GlobalTheory.LevCmp.ValDelta
variable {D : D7}
theorem locComp_of_isRc_classMapD_cenLoc : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ B _ T w P x => ∀ (l : _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x) (v : B.places.Pl) (i : (Dof x).ntw.Tw) (b : Bool) (ψ : G (Dof x).host.E (Dof x).nd.Om →* ((Dof x).ntw.Ok i (T.k v))ˣ) (hA : NX.AdmTw (Dof x) i (T.k v) (QOf P v) ψ) (j : Fin (Dof x).R.m), TwistedAt (Dof x) v → (Dof x).ntw.l i = B.places.resChar v → IntegralHeckeForms.TwOK i (T.k v) (QOf P v) ψ → ∀ e, SideRead i b (T.k v) e → ReadsHecke e ψ (T.psi v) → ∀ P' ∈ (cell (D := Dof x) l.b.Bs.exp b hA j).DP, ∀ (a : 𝓞 (Dof x).host.E) (k : (Dof x).host.Eˣ), a ∉ P'.asIdeal → (k : (Dof x).host.E) = (a : (Dof x).host.E) → e (NX.ofO0 (Dof x) i (T.k v) (NX.tameVal ((Dof x).ntw.delta i) P' (if b then l.b.Bs.exp.sgnT else -l.b.Bs.exp.sgnT) a).1) = (((eta (D := Dof x) (cfOf x) w.I.xi v j).locK P' k : ℂˣ) : ℂ) := by
  intro hP hL
  refine GlobalTheory.Mem.Top.Bl.StepW.of_all ?_
  intro K B f T w _ _ _ P x l v i b ψ hA j htw hl hok e he _ P' hP' a k ha hk
  have h2 := P.q.mu.tw v
  have hp : P' ∈ (Dof x).ntw.pD i := (cell (D := Dof x) l.b.Bs.exp b hA j).DP_sub hP'
  obtain ⟨hxu, hv⟩ := tameVal_delta hP.what₂.art (cfOf x) l.b.Bs.deltaRead he hp a k ha hk
  rw [l.b.Bs.exp.sgnT_one]
  refine hv.trans (congrArg Units.val ?_)
  have hp' : P' ∈ placesOver (Dof x).host.E (if (Dof x).ntw.l i = (Dof x).host.pde then (Dof x).host.pde' else (Dof x).host.pde) := by
    rw [← (Dof x).ntw.pD_eq i]; exact hp
  obtain ⟨h1, -, h3, -, -⟩ := GlobalTheory.GalChar.inertialOrderFifteenChar_auxiliaryPrime_spec (GlobalTheory.Triple.hframe (cfOf x)) (l := (Dof x).ntw.l i)
  have hmu : ((cfOf x).mu0 j).UnrAt P' :=
    ((cfOf x).isMu0 j).unr P' fun kk => GlobalTheory.GalChar.notMem_of_ne h1 ((Dof x).host.g_prime kk) (h3 kk) hp'
  have hψ : (T.psi v).UnrAt P' := by
    change P' ∈ placesOver B.host.E (if (Dof x).ntw.l i = B.host.pde then B.host.pde' else B.host.pde) at hp'
    split_ifs at hp'
    · exact BadV.unr_of_twist (T.psi_tw v) B.host.pde'_prime (by simp [offSet]) P' hp'
    · exact BadV.unr_of_twist (T.psi_tw v) B.host.pde_prime (by simp [offSet]) P' hp'
  have hdel : (cfOf x).delAt ((Dof x).ntw.l i) = if B.places.resChar v = B.host.pde then f.del' else f.del := by
    rw [hl]
    exact congrArg (fun c : Top.Fr B.toPre => if B.places.resChar v = B.host.pde then c.del' else c.del) w.C_eq
  have key : ∀ (u : HeightOneSpectrum (𝓞 B.host.E)) (μ δ ξ : HChar B.host.E) (y), IsUnitAt u y → μ.UnrAt u → ξ.UnrAt u →
      δ.loc u y = (μ * (δ * ξ)).loc u y := by
    intro u μ δ ξ y hy h1 h2
    rw [HChar.loc_mul, HChar.loc_mul, h1 _ hy, h2 _ hy, one_mul, mul_one]
  rw [hdel]
  exact (key P' _ _ _ _ hxu hmu hψ).trans
    (congrArg (fun ξ : HChar B.host.E => (@HMul.hMul (HChar B.host.E) (HChar B.host.E) _ _ ((cfOf x).mu0 j) ξ).loc P' (atFin P' k)) h2.symm)
end GlobalTheory.LevCmp.ValDelta
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conductor_valuation_delta_le_of_sideRead : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ B _ T w P x => ∀ (l : _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x) (v : B.places.Pl) (i : (Dof x).ntw.Tw) (b : Bool) (ψ : G (Dof x).host.E (Dof x).nd.Om →* ((Dof x).ntw.Ok i (T.k v))ˣ) (hA : NX.AdmTw (Dof x) i (T.k v) (QOf P v) ψ) (j : Fin (Dof x).R.m), TwistedAt (Dof x) v → (Dof x).ntw.l i = B.places.resChar v → IntegralHeckeForms.TwOK i (T.k v) (QOf P v) ψ → ∀ e, SideRead i b (T.k v) e → ReadsHecke e ψ (T.psi v) → ∀ P' ∈ (cell (D := Dof x) l.b.Bs.exp b hA j).DP, ∀ (a : 𝓞 (Dof x).host.E) (k : (Dof x).host.Eˣ), a ∉ P'.asIdeal → (k : (Dof x).host.E) = (a : (Dof x).host.E) → e (NX.ofO0 (Dof x) i (T.k v) (NX.tameVal ((Dof x).ntw.delta i) P' (if b then l.b.Bs.exp.sgnT else -l.b.Bs.exp.sgnT) a).1) = (((eta (D := Dof x) (cfOf x) w.I.xi v j).locK P' k : ℂˣ) : ℂ) := by
  first | exact @_root_.GlobalTheory.LevCmp.ValDelta.locComp_of_isRc_classMapD_cenLoc | exact _root_.GlobalTheory.LevCmp.ValDelta.locComp_of_isRc_classMapD_cenLoc | (intros; apply _root_.GlobalTheory.LevCmp.ValDelta.locComp_of_isRc_classMapD_cenLoc <;> assumption)
end
end
