import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrActApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiltrationStepFromSectionKernelStatement

noncomputable section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg GlobalTheory.SteepMult

namespace GlobalTheory.SteepMult

theorem section1_mem_orthogonal_ker : ∀ (R S : ℕ) (M : GKMod R S) (N : Submodule ℂ M.V), KStable M.act N →
    ∀ (B : N →ₗ⋆[ℂ] N →ₗ[ℂ] ℂ) (k : ℕ) (Ψ : (Fin (k + 1) → NC R S) → N),
    Ψ ∈ ((filt M.act N k).comap (phiN M.act N (k + 1))).orthogonalBilin (formT (k + 1) B) →
    ∀ i g, section1 Ψ i g ∈ (LinearMap.ker (phiN M.act N 1)).orthogonalBilin (formT 1 B) := by
  intro R S M N hN B k Ψ hΨ i g
  classical
  rw [Submodule.mem_orthogonalBilin_iff]
  intro x hx
  let Φ : (Fin (k + 1) → NC R S) → N := fun g' =>
    if ∀ j, j ≠ i → g' j = g j then x (fun _ => g' i) else 0
  have hΦ : Φ ∈ (filt M.act N k).comap (phiN M.act N (k + 1)) := by
    rw [Submodule.mem_comap]
    apply GlobalTheory.T.filtration_step_from_section_kernel R S M N hN k i Φ
    intro g''
    by_cases h : ∀ j, j ≠ i → g'' j = g j
    · have e : section1 Φ i g'' = x := by
        funext h'
        simp only [section1, Φ]
        rw [if_pos (fun j hj => by rw [Function.update_of_ne hj]; exact h j hj)]
        simp only [Function.update_self]
        congr 1
        funext j
        rw [Subsingleton.elim j 0]
      rw [e]
      exact hx
    · have e : section1 Φ i g'' = 0 := by
        funext h'
        simp only [section1, Φ]
        rw [if_neg]
        · rfl
        · intro hc
          apply h
          intro j hj
          have := hc j hj
          rwa [Function.update_of_ne hj] at this
      rw [e, map_zero]
  have h0 : formT (k + 1) B Φ Ψ = 0 := (Submodule.mem_orthogonalBilin_iff.1 hΨ) Φ hΦ
  have key : formT (k + 1) B Φ Ψ = ∑ y, B (x (fun _ => y)) (Ψ (Function.update g i y)) := by
    rw [formT_apply, ← Finset.sum_subset (Finset.subset_univ (Finset.univ.image (Function.update g i)))]
    · rw [Finset.sum_image (fun a _ b _ hab => Function.update_injective g i hab)]
      refine Finset.sum_congr rfl fun y _ => ?_
      simp only [Φ]
      rw [if_pos (fun j hj => Function.update_of_ne hj _ _)]
      simp only [Function.update_self]
    · intro g' _ hg'
      simp only [Φ]
      rw [if_neg, map_zero, LinearMap.zero_apply]
      intro hc
      apply hg'
      rw [Finset.mem_image]
      refine ⟨g' i, Finset.mem_univ _, ?_⟩
      funext j
      by_cases hj : j = i
      · subst hj; simp
      · rw [Function.update_of_ne hj, hc j hj]
  show formT 1 B x (section1 Ψ i g) = 0
  rw [key] at h0
  rw [formT_apply]
  refine (Fintype.sum_equiv (Equiv.funUnique (Fin 1) (NC R S)) _ _ fun h => ?_).trans h0
  simp only [section1, Equiv.funUnique_apply]
  congr 2
  congr 1
  funext j
  rw [Subsingleton.elim j default]

end GlobalTheory.SteepMult

end
