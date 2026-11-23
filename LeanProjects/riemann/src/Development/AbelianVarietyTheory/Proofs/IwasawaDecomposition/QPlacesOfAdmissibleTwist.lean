import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsHecke
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComapRealSubfieldEqIffEqOrIsConjPlace
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

namespace GlobalTheory.LevCmp.ParaPlace

theorem unr_mul {L : Type} [Field L] [NumberField L] {χ χ' : HChar L} {u : HeightOneSpectrum (𝓞 L)}
    (h : χ.UnrAt u) (h' : χ'.UnrAt u) : (χ * χ').UnrAt u := fun y hy => by
  rw [HChar.loc_mul, h y hy, h' y hy, one_mul]

theorem main : PrN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AllSt fun _ B _ T w P x => ∀ (l : StrictHenselianAcyclic hL x) (v : B.places.Pl) (i : (Dof x).ntw.Tw) (b : Bool) (ψ : G (Dof x).host.E (Dof x).nd.Om →* ((Dof x).ntw.Ok i (T.k v))ˣ) (hA : NX.AdmTw (Dof x) i (T.k v) (QOf P v) ψ) (j : Fin (Dof x).R.m), TwistedAt (Dof x) v → (Dof x).ntw.l i = B.places.resChar v → IntegralHeckeForms.TwOK i (T.k v) (QOf P v) ψ → ∀ u ∈ qPl (Dof x) (eta (D := Dof x) (cfOf x) w.I.xi v j), ∃ P' : PlE (Dof x).host, (P' ∈ (cell (D := Dof x) l.b.Bs.exp b hA j).QP ∨ P' ∈ (cell (D := Dof x) l.b.Bs.exp b hA j).DP) ∧ ((cell (D := Dof x) l.b.Bs.exp b hA j).sp P').v = u := by
  intro _ hL
  refine GlobalTheory.Mem.Top.Bl.StepW.of_all ?_
  intro K B f T w _ _ _ P x l v i b ψ hA j htw hl hok
  have hQ : QOf P v = T.Q v := GlobalTheory.HeightCounting.Up.Model.qOf_eq v
  have h2 := P.q.mu.tw v
  intro u hu
  obtain ⟨hg, w', hw'u, hun⟩ := hu
  have hmu : ((cfOf x).mu0 j).UnrAt w' :=
    ((cfOf x).isMu0 j).unr w' fun k hk => hg ⟨w', hw'u, k, hk⟩
  have hxi : ¬ (T.xiTw f v).UnrAt w' := by
    intro hx
    rw [← h2] at hx
    exact hun (unr_mul hmu hx)
  unfold TwDat.xiTw at hxi
  set M := cell (D := Dof x) l.b.Bs.exp b hA j
  have fin : ∀ P' : PlE (Dof x).host, (P' ∈ M.QP ∨ P' ∈ M.DP) → (w' = P' ∨ IsConjPl (Dof x).host w' P') →
      ∃ P' : PlE (Dof x).host, (P' ∈ M.QP ∨ P' ∈ M.DP) ∧ (M.sp P').v = u := by
    intro P' hP' hc
    refine ⟨P', hP', ?_⟩
    have hw := M.sp_w P' (hP'.elim Or.inl (fun h => Or.inr (Or.inl h)))
    have hov : NG.OverPl P' u := by
      have e := (GlobalTheory.PlacePair.comap_eq_iff (Dof x) w' P').2 hc
      exact e.symm.trans hw'u
    apply HeightOneSpectrum.ext
    exact (M.sp P').w_under.symm.trans (by rw [hw]; exact hov)
  by_cases hq : w' ∈ T.Q v
  · obtain ⟨P', hP', hc⟩ := M.QP_cover w' (hQ ▸ hq)
    exact fin P' (Or.inl hP') (hc.imp Eq.symm id)
  · have hψ : (T.psi v).UnrAt w' := ((T.psi_is v).ram w').2 hq
    have hd := fun h => hxi (unr_mul h hψ)
    have hp : w' ∈ (Dof x).ntw.pD i := by
      rw [← Finset.mem_coe, (Dof x).ntw.pD_eq i, hl]
      change w' ∈ placesOver B.host.E (if B.places.resChar v = B.host.pde then B.host.pde' else B.host.pde)
      split_ifs at hd ⊢
      · by_contra ho; exact hd (f.isDel'.unr w' ho)
      · by_contra ho; exact hd (f.isDel.unr w' ho)
    obtain ⟨P', hP', hc⟩ := M.DP_cover w' hp
    exact fin P' (Or.inr hP') (hc.imp Eq.symm id)

end GlobalTheory.LevCmp.ParaPlace
