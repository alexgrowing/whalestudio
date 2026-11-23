import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsHeckeOfSideReadStatement
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
namespace GlobalTheory.LevCmp.ValQ
theorem locComp_of_isRc_classMapD_cenLoc : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ B _ T w P x => ∀ (l : _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x) (v : B.places.Pl) (i : (Dof x).ntw.Tw) (b : Bool) (ψ : G (Dof x).host.E (Dof x).nd.Om →* ((Dof x).ntw.Ok i (T.k v))ˣ) (hA : NX.AdmTw (Dof x) i (T.k v) (QOf P v) ψ) (j : Fin (Dof x).R.m), TwistedAt (Dof x) v → (Dof x).ntw.l i = B.places.resChar v → IntegralHeckeForms.TwOK i (T.k v) (QOf P v) ψ → ∀ e, SideRead i b (T.k v) e → ReadsHecke e ψ (T.psi v) → ∀ P' ∈ (cell (D := Dof x) l.b.Bs.exp b hA j).QP, ∀ (a : 𝓞 (Dof x).host.E) (k : (Dof x).host.Eˣ), a ∉ P'.asIdeal → (k : (Dof x).host.E) = (a : (Dof x).host.E) → e (NX.ofOk (Dof x) i (T.k v) (NX.tameVal ψ P' l.b.Bs.exp.sgnT a).1) = (((eta (D := Dof x) (cfOf x) w.I.xi v j).locK P' k : ℂˣ) : ℂ) := by
  intro hP hL
  refine GlobalTheory.Mem.Top.Bl.StepW.of_all ?_
  intro K B f T w _ _ _ P x l v i b ψ hA j htw hl hok e hside hR P' hP' a y ha hy
  have h2 := P.q.mu.tw v
  have hPQ : P' ∈ QOf P v := (cell (D := Dof x) l.b.Bs.exp b hA j).QP_sub hP'
  have hlP := (hA.1 P' hPQ).2
  have hpD := (hA.2.1 P' hPQ).1
  have hg := (hA.2.1 P' hPQ).2
  have hmu : ((cfOf x).mu0 j).UnrAt P' := ((cfOf x).isMu0 j).unr P' fun k hk => hg k hk
  have hxu : IsUnitAt P' (atFin P' y) := by
    show Valued.v (((y : (Dof x).host.E) : P'.adicCompletion (Dof x).host.E)) = 1
    rw [hy, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact (HeightOneSpectrum.valuation_eq_one_iff_notMem _).2 ha
  rw [l.b.Bs.exp.sgnT_one, tameVal_eq_locK hP.what₂.art (Dof x) i (T.k v) e ψ (T.psi v) hR hA.2.2.1 hA.2.2.2.2.1 P' hlP a y ha hy]
  have hp' : P' ∉ placesOver B.host.E (if B.places.resChar v = B.host.pde then B.host.pde' else B.host.pde) := by
    intro h
    apply hpD
    rw [← Finset.mem_coe, (Dof x).ntw.pD_eq i, hl]
    exact h
  show _ = ((((cfOf x).mu0 j).loc P' (atFin P' y) * (w.I.xi ((Dof x).what₂.muTw v)).loc P' (atFin P' y) : ℂˣ) : ℂ)
  rw [hmu _ hxu, one_mul]
  have h3 : w.I.xi ((Dof x).what₂.muTw v) = T.xiTw f v := h2
  rw [h3]
  unfold TwDat.xiTw
  split_ifs with hc
  · rw [if_pos hc] at hp'
    have hd := f.isDel'.unr P' hp' _ hxu
    show _ = (((f.del'.loc P') ((atFin P') y) * ((T.psi v).loc P') ((atFin P') y) : ℂˣ) : ℂ)
    rw [hd, one_mul]
    rfl
  · rw [if_neg hc] at hp'
    have hd := f.isDel.unr P' hp' _ hxu
    show _ = (((f.del.loc P') ((atFin P') y) * ((T.psi v).loc P') ((atFin P') y) : ℂˣ) : ℂ)
    rw [hd, one_mul]
    rfl
end GlobalTheory.LevCmp.ValQ
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
theorem _root_.GlobalTheory.T.conductor_valuation_q_le_of_sideRead : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ B _ T w P x => ∀ (l : _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x) (v : B.places.Pl) (i : (Dof x).ntw.Tw) (b : Bool) (ψ : G (Dof x).host.E (Dof x).nd.Om →* ((Dof x).ntw.Ok i (T.k v))ˣ) (hA : NX.AdmTw (Dof x) i (T.k v) (QOf P v) ψ) (j : Fin (Dof x).R.m), TwistedAt (Dof x) v → (Dof x).ntw.l i = B.places.resChar v → IntegralHeckeForms.TwOK i (T.k v) (QOf P v) ψ → ∀ e, SideRead i b (T.k v) e → ReadsHecke e ψ (T.psi v) → ∀ P' ∈ (cell (D := Dof x) l.b.Bs.exp b hA j).QP, ∀ (a : 𝓞 (Dof x).host.E) (k : (Dof x).host.Eˣ), a ∉ P'.asIdeal → (k : (Dof x).host.E) = (a : (Dof x).host.E) → e (NX.ofOk (Dof x) i (T.k v) (NX.tameVal ψ P' l.b.Bs.exp.sgnT a).1) = (((eta (D := Dof x) (cfOf x) w.I.xi v j).locK P' k : ℂˣ) : ℂ) := by
  first | exact @_root_.GlobalTheory.LevCmp.ValQ.locComp_of_isRc_classMapD_cenLoc | exact _root_.GlobalTheory.LevCmp.ValQ.locComp_of_isRc_classMapD_cenLoc | (intros; apply _root_.GlobalTheory.LevCmp.ValQ.locComp_of_isRc_classMapD_cenLoc <;> assumption)
end
end
