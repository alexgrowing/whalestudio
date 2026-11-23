import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.TensorProductVectors

noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ

namespace ParabolicMaximalCompact

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem leviProj_mem_KO {s n : ℕ} (d : Fin s → ℕ) (hd : ∑ a, d a = n) (p : parab k (stdBlocks d hd))
    (hp : (p : GL (Fin n) k) ∈ KO k (Fin n)) (a : Fin s) :
    leviProj k (stdBlocks d hd) p a ∈ KO k (Fin (d a)) := by
  rw [GlobalTheory.StepData.mem_KO] at hp ⊢
  have hinv : ((GlobalTheory.SmGL.leviProj k (GlobalTheory.SmGL.stdBlocks d hd) p a)⁻¹ :
      GL (Fin (d a)) k) =
      GlobalTheory.SmGL.leviProj k (GlobalTheory.SmGL.stdBlocks d hd) p⁻¹ a := by
    rw [map_inv, Pi.inv_apply]
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [GlobalTheory.SmGL.leviProj_apply]
    exact hp.1 _ _
  · rw [hinv, GlobalTheory.SmGL.leviProj_apply]
    exact hp.2 _ _

end ParabolicMaximalCompact

theorem step_parabKO : ParabolicInductionKernel := by
  intro k _ _ _ _ s n d hd p hp
  have h := fun a => ParabolicMaximalCompact.leviProj_mem_KO d hd p hp a
  exact ⟨h, deltaHalf_of_mem_leviK ((Subgroup.mem_pi _).2 fun a _ => h a)⟩

end UpperTheory.TNZ
