import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsHecke
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

noncomputable section

namespace GlobalTheory.TwTameCell

theorem tameAt_mul {L : Type} [Field L] [NumberField L] {χ χ' : HChar L} {v : HeightOneSpectrum (𝓞 L)}
    (h : χ.TameAt v) (h' : χ'.TameAt v) : (χ * χ').TameAt v := fun y hy hy1 => by
  rw [HChar.loc_mul, h y hy hy1, h' y hy hy1, mul_one]

theorem tameAt_one {L : Type} [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 L)) : (1 : HChar L).TameAt v :=
  fun _ _ _ => rfl

theorem eta_tameAt : PrN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AllSt fun _ B _ T w P x => ∀ (l : StrictHenselianAcyclic hL x) (v : B.places.Pl) (i : (Dof x).ntw.Tw) (b : Bool) (ψ : G (Dof x).host.E (Dof x).nd.Om →* ((Dof x).ntw.Ok i (T.k v))ˣ) (hA : NX.AdmTw (Dof x) i (T.k v) (QOf P v) ψ) (j : Fin (Dof x).R.m), TwistedAt (Dof x) v → (Dof x).ntw.l i = B.places.resChar v → IntegralHeckeForms.TwOK i (T.k v) (QOf P v) ψ → ∀ P' : PlE (Dof x).host, (P' ∈ (cell (D := Dof x) l.b.Bs.exp b hA j).QP ∨ P' ∈ (cell (D := Dof x) l.b.Bs.exp b hA j).DP) → (eta (D := Dof x) (cfOf x) w.I.xi v j).TameAt P' := by
  intro _ hL
  refine StepW.of_all ?_
  intro K B f T w _ _ _ P x l v i b ψ hA j _ _ _ P' _
  have h1 := ((cfOf x).isMu0 j).tame P'
  have hx : w.I.xi ((Dof x).what₂.muTw v) ∈ T.set f := w.xi_range ▸ Set.mem_range_self _
  simp only [TwDat.set, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range] at hx
  have h2 : (w.I.xi ((Dof x).what₂.muTw v)).TameAt P' := by
    rcases hx with (h | h | h) | ⟨w', h⟩
    · rw [h]; exact tameAt_one P'
    · rw [h]; exact f.isDel.tame P'
    · rw [h]; exact f.isDel'.tame P'
    · rw [← h]
      unfold TwDat.xiTw
      split_ifs
      · exact tameAt_mul (f.isDel'.tame P') ((T.psi_is w').tame P')
      · exact tameAt_mul (f.isDel.tame P') ((T.psi_is w').tame P')
  exact tameAt_mul h1 h2

end GlobalTheory.TwTameCell

end
