import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.T2SpaceMatrixOfIsNonarchimedeanLocalField

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.TensSB

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n n' : Type}

theorem of_tensCol_mem {Ψ : Matrix n n' k → ℂ} {a : (n → k) → ℂ}
    (h : tensCol Ψ a ∈ SB (Matrix n (n' ⊕ Fin 1) k)) (ha : a ≠ 0) : Ψ ∈ SB (Matrix n n' k) := by
  haveI := Comm.t2Space_matrix_of_isNonarchimedeanLocalField (k := k) (n := n) (n' := n')
  obtain ⟨y₀, hy₀⟩ : ∃ y₀, a y₀ ≠ 0 := by
    by_contra h0
    push_neg at h0
    exact ha (funext h0)
  have hg := Comm.comp_mem_SB h
    (p := fun x₀ : Matrix n n' k => Matrix.of fun i j => Sum.elim (x₀ i) (fun _ => y₀ i) j)
    (s := fun x : Matrix n (n' ⊕ Fin 1) k => x.submatrix id Sum.inl) ?_ (by fun_prop) (fun x₀ => rfl)
  · have e : Ψ = (a y₀)⁻¹ • fun x₀ : Matrix n n' k =>
        tensCol Ψ a (Matrix.of fun i j => Sum.elim (x₀ i) (fun _ => y₀ i) j) := by
      funext x₀
      show Ψ x₀ = (a y₀)⁻¹ * (Ψ x₀ * a y₀)
      field_simp
    rw [e]
    exact Submodule.smul_mem _ _ hg
  · refine continuous_matrix fun i j => ?_
    rcases j with j | j
    · exact continuous_id.matrix_elem i j
    · exact continuous_const

theorem of_tensRow_mem {Ψ : Matrix n n' k → ℂ} {b : (n' → k) → ℂ}
    (h : tensRow Ψ b ∈ SB (Matrix (n ⊕ Fin 1) n' k)) (hb : b ≠ 0) : Ψ ∈ SB (Matrix n n' k) := by
  haveI := Comm.t2Space_matrix_of_isNonarchimedeanLocalField (k := k) (n := n) (n' := n')
  obtain ⟨η₀, hη₀⟩ : ∃ η₀, b η₀ ≠ 0 := by
    by_contra h0
    push_neg at h0
    exact hb (funext h0)
  have hg := Comm.comp_mem_SB h
    (p := fun x₀ : Matrix n n' k => Matrix.of fun i j => Sum.elim (fun i => x₀ i j) (fun _ => η₀ j) i)
    (s := fun x : Matrix (n ⊕ Fin 1) n' k => x.submatrix Sum.inl id) ?_ (by fun_prop) (fun x₀ => rfl)
  · have e : Ψ = (b η₀)⁻¹ • fun x₀ : Matrix n n' k =>
        tensRow Ψ b (Matrix.of fun i j => Sum.elim (fun i => x₀ i j) (fun _ => η₀ j) i) := by
      funext x₀
      show Ψ x₀ = (b η₀)⁻¹ * (Ψ x₀ * b η₀)
      field_simp
    rw [e]
    exact Submodule.smul_mem _ _ hg
  · refine continuous_matrix fun i j => ?_
    rcases i with i | i
    · exact continuous_id.matrix_elem i j
    · exact continuous_const

end GlobalTheory.FinPl.TensSB

namespace GlobalTheory.FinPl

theorem tens_SB_iff : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'],
    (∀ (Ψ : Matrix n n' k → ℂ) (a : (n → k) → ℂ), Ψ ∈ SB (Matrix n n' k) → a ∈ SB (n → k) → tensCol Ψ a ∈ SB (Matrix n (n' ⊕ Fin 1) k)) ∧
    (∀ (Ψ : Matrix n n' k → ℂ) (a : (n → k) → ℂ), tensCol Ψ a ∈ SB (Matrix n (n' ⊕ Fin 1) k) → a ≠ 0 → Ψ ∈ SB (Matrix n n' k)) ∧
    (∀ (Ψ : Matrix n' n k → ℂ) (b : (n → k) → ℂ), Ψ ∈ SB (Matrix n' n k) → b ∈ SB (n → k) → tensRow Ψ b ∈ SB (Matrix (n' ⊕ Fin 1) n k)) ∧
    (∀ (Ψ : Matrix n' n k → ℂ) (b : (n → k) → ℂ), tensRow Ψ b ∈ SB (Matrix (n' ⊕ Fin 1) n k) → b ≠ 0 → Ψ ∈ SB (Matrix n' n k)) := by
  intro k _ _ _ _ n n' _ _ _ _
  exact ⟨fun Ψ a hΨ ha => Comm.tensCol_mem hΨ ha, fun Ψ a h ha => TensSB.of_tensCol_mem h ha,
    fun Ψ b hΨ hb => Comm.tensRow_mem hΨ hb, fun Ψ b h hb => TensSB.of_tensRow_mem h hb⟩

end GlobalTheory.FinPl

end
