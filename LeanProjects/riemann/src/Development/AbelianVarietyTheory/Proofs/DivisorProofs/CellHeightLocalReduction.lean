import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipLeviProj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsColReduced
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsOpenSetOfLeRank

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.WhitHered Matrix Topology Pointwise

namespace GlobalTheory.WhitHered.CellLoc

section Alg

variable {k : Type} [Field k] {N : ℕ}

def pm (σ : Equiv.Perm (Fin N)) : GL (Fin N) k :=
  ⟨Matrix.of fun a c => if a = σ c then 1 else 0, Matrix.of fun a c => if c = σ a then 1 else 0, by
    ext a c
    rw [Matrix.mul_apply, Finset.sum_eq_single (σ.symm a)]
    · simp [Matrix.one_apply, eq_comm]
    · intro b _ hb
      have : a ≠ σ b := fun h => hb (by simp [h])
      simp [this]
    · simp, by
    ext a c
    simp [Matrix.mul_apply, Matrix.one_apply, eq_comm]⟩

end Alg

section Main

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {N c : ℕ} {m : Fin c → ℕ}

theorem isClosed_parab (e : (Σ a, Fin (m a)) ≃ Fin N) : IsClosed (parab k e : Set (GL (Fin N) k)) := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have : (parab k e : Set (GL (Fin N) k)) = ⋂ i, ⋂ j, ⋂ _ : blk e j < blk e i, {g : GL (Fin N) k | g.val i j = 0} := by
    ext g
    simp only [SetLike.mem_coe, mem_parab, Set.mem_iInter, Set.mem_setOf_eq]
  rw [this]
  exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
    isClosed_eq (Units.continuous_val.matrix_elem i j) continuous_const

end Main

end GlobalTheory.WhitHered.CellLoc

end
