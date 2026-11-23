import Mathlib
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CanonListLength
open CategoryTheory Polynomial

noncomputable section

namespace GlobalTheory.SerCmp.ListBlocks

open Formalism.IrreducibleCountingLemmas.TYPES

theorem glEquiv_transp_cancel {g : ℕ} [Fact g.Prime] {F : Type} [Fintype F] [DecidableEq F] {n : ℕ}
    (E : F ≃ Fin n) (x : GL (Fin n) (ZMod g)) :
    (glEquiv (ZMod g) E.symm).symm ((glEquiv (ZMod g) E).symm x) = x := by
  ext i j
  rw [Formalism.L2.PT.coe_glEquiv_symm, Formalism.L2.PT.coe_glEquiv_symm]
  simp

theorem entry_eq {g : ℕ} [Fact g.Prime] {F : Type} [Fintype F] [DecidableEq F] {d : ℕ}
    (h : Fintype.card F = d) (V : FDRep ℂ (GL (Fin d) (ZMod g))) :
    (⟨Fintype.card F, fun x => (transp (Fintype.equivFin F)
      (transp ((finCongr h.symm).trans (Fintype.equivFin F).symm) V)).character x⟩ : GlobalTheory.GLq.Pc g) =
      ⟨d, fun x => V.character x⟩ := by
  generalize Fintype.equivFin F = E
  subst h
  refine Sigma.ext rfl (heq_of_eq (funext fun x => ?_))
  dsimp only
  rw [Formalism.L2.PT.character_transp, Formalism.L2.PT.character_transp]
  congr 1
  have : (finCongr (rfl : Fintype.card F = Fintype.card F)).trans E.symm = E.symm := by ext; simp
  rw [this, glEquiv_transp_cancel]

theorem exists_blocks (s : ℕ) (d : Fin s → ℕ) (r : ℕ) (hr : ∑ c, d c = r) :
    ∃ b : Fin r → Fin s, ∀ c, Fintype.card {i // b i = c} = d c := by
  subst hr
  refine ⟨fun i => (finSigmaFinEquiv.symm i).1, fun c => ?_⟩
  rw [Fintype.card_congr ((finSigmaFinEquiv.symm.subtypeEquiv (fun _ => Iff.rfl)).trans (Equiv.sigmaSubtype c))]
  simp

end GlobalTheory.SerCmp.ListBlocks

open Formalism.IrreducibleCountingLemmas.TYPES in
theorem GlobalTheory.SerCmp.canonList_of_cuspidal_list : ∀ (g : ℕ) [Fact g.Prime] (Q : List (GlobalTheory.GLq.Pc g)), (∀ p ∈ Q, 1 ≤ p.1 ∧ ∃ V : FDRep ℂ (GL (Fin p.1) (ZMod g)), CategoryTheory.Simple V ∧ Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal (ZMod g) V ∧ ∀ x, V.character x = p.2 x) → ∃ (b : Fin (GlobalTheory.GLq.degL Q) → Fin Q.length) (lam : ∀ c : Fin Q.length, FDRep ℂ (GL {i // b i = c} (ZMod g))), Function.Surjective b ∧ (∀ c, CategoryTheory.Simple (lam c) ∧ Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal (ZMod g) (lam c)) ∧ GlobalTheory.SerCmp.canonList b lam = Q := by
  intro g _ Q hQ
  have H : ∀ c : Fin Q.length, ∃ V : FDRep ℂ (GL (Fin (Q.get c).1) (ZMod g)), 1 ≤ (Q.get c).1 ∧
      CategoryTheory.Simple V ∧ IsCuspidal (ZMod g) V ∧ ∀ x, V.character x = (Q.get c).2 x := by
    intro c
    obtain ⟨h1, V, h2⟩ := hQ _ (List.get_mem Q c)
    exact ⟨V, h1, h2⟩
  choose V hd hVs hVc hVch using H
  have hsum : ∑ c : Fin Q.length, (Q.get c).1 = GlobalTheory.GLq.degL Q := by
    rw [GlobalTheory.GLq.degL]
    rw [← Fin.sum_univ_getElem]
    exact Fintype.sum_equiv (finCongr (List.length_map _).symm) _ _ (fun c => by simp)
  obtain ⟨b, hcard⟩ := GlobalTheory.SerCmp.ListBlocks.exists_blocks Q.length (fun c => (Q.get c).1) _ hsum
  refine ⟨b, fun c => transp ((finCongr (hcard c).symm).trans (Fintype.equivFin _).symm) (V c), ?_, ?_, ?_⟩
  · intro c
    have : 0 < Fintype.card {i // b i = c} := by rw [hcard c]; exact hd c
    obtain ⟨⟨i, hi⟩⟩ := Fintype.card_pos_iff.1 this
    exact ⟨i, hi⟩
  · intro c
    exact ⟨Formalism.L2.PT.simple_transp _ (hVs c), Formalism.L2.PT.isCuspidal_transp _ (hVc c)⟩
  · apply List.ext_get (GlobalTheory.SerCmp.canonList_length _ _)
    intro n h1 h2
    simp only [GlobalTheory.SerCmp.canonList, List.get_eq_getElem, List.getElem_map, List.getElem_finRange]
    rw [GlobalTheory.SerCmp.ListBlocks.entry_eq (hcard _) (V _)]
    have key : ∀ c, (⟨(Q.get c).1, fun x => (V c).character x⟩ : GlobalTheory.GLq.Pc g) = Q.get c := fun c =>
      Sigma.ext rfl (heq_of_eq (_root_.funext fun x => hVch c x))
    rw [key]
    simp
