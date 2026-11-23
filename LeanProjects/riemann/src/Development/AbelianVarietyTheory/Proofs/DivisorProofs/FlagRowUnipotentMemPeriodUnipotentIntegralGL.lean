import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrdL

open GlobalTheory.FunObj GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.DiagVol ValuativeRel Matrix

namespace GlobalTheory.DiagVol

theorem rowElt_mem : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} (t : n ⊕ Fin c) (y : n ⊕ Fin c → k),
    (∀ s, y s ∈ 𝒪[k]) → (∀ s, ¬ ordL c t < ordL c s → y s = 0) →
    ∃ x ∈ symN k n c ⊓ KO k (n ⊕ Fin c), x.val = 1 + Matrix.of (fun r s => if r = t then y s else 0) := by
  intro k _ _ _ _ n _ _ c t y hy h0
  set E : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k := Matrix.of (fun r s => if r = t then y s else 0) with hE
  have yt : y t = 0 := h0 t (lt_irrefl _)
  have hEE : E * E = 0 := by
    ext r s
    simp [hE, Matrix.mul_apply, yt]
  have h1 : (1 + E) * (1 - E) = 1 := by
    simp only [add_mul, mul_sub, one_mul, mul_one, hEE]; abel
  have h2 : (1 - E) * (1 + E) = 1 := by
    simp only [sub_mul, mul_add, one_mul, mul_one, hEE]; abel
  let M : GL (n ⊕ Fin c) k := ⟨1 + E, 1 - E, h1, h2⟩
  refine ⟨M, Subgroup.mem_inf.2 ⟨?_, ?_⟩, rfl⟩
  · have key : ∀ p, (∀ s, lev p s ≤ lev p t → y s = 0) → M ∈ N k n c p := by
      intro p hp
      rw [Model.mem_N_iff]
      intro r s hrs
      show (1 + E) r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s
      rw [Matrix.add_apply, hE, Matrix.of_apply]
      split_ifs with hr
      · subst hr; rw [hp s hrs, add_zero]
      · rw [add_zero]
    unfold symN
    rcases t with x | i
    · refine Subgroup.mem_sup_left (key _ fun s hs => h0 s ?_)
      rcases s with z | j <;> simp [ordL, lev] at hs ⊢ <;> omega
    · refine Subgroup.mem_sup_right (key _ fun s hs => h0 s ?_)
      rcases s with z | j <;> simp [ordL, lev] at hs ⊢ <;> omega
  · rw [mem_KO_iff]
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · show (1 + E) i j ∈ 𝒪[k]
      simp only [Matrix.add_apply, hE, Matrix.of_apply, Matrix.one_apply]
      refine add_mem ?_ ?_ <;> split_ifs <;> first | exact one_mem _ | exact zero_mem _ | exact hy _
    · show (1 - E) i j ∈ 𝒪[k]
      simp only [Matrix.sub_apply, hE, Matrix.of_apply, Matrix.one_apply]
      refine sub_mem ?_ ?_ <;> split_ifs <;> first | exact one_mem _ | exact zero_mem _ | exact hy _

end GlobalTheory.DiagVol
