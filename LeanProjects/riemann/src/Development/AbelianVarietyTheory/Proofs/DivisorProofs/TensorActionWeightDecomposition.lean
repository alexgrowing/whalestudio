import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrActApply
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg GlobalTheory.SteepMult

namespace GlobalTheory.SteepMult

lemma adP_Eab_self {R S : ℕ} (c : Ix R S) (y x : NC R S) :
    adP (Eab c c) y x = if x = y then ((if y.1.1 = c then 1 else 0) - (if y.1.2 = c then 1 else 0) : ℂ) else 0 := by
  obtain ⟨⟨a, b⟩, h⟩ := x
  obtain ⟨⟨a', b'⟩, h'⟩ := y
  simp only [adP, Eab, Matrix.single_apply, Subtype.mk.injEq, Prod.mk.injEq]
  by_cases h1 : a = a' <;> by_cases h2 : b = b' <;> by_cases h3 : c = a' <;> by_cases h4 : c = b' <;>
    simp_all [eq_comm] <;> grind

lemma tAct_Eab_self_apply {R S k : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W] (actW : Mat R S →ₗ[ℂ] Module.End ℂ W)
    (c : Ix R S) (Ψ : (Fin k → NC R S) → W) (g : Fin k → NC R S) :
    tAct k actW (Eab c c) Ψ g = actW (Eab c c) (Ψ g) +
      (∑ i, ((if (g i).1.1 = c then 1 else 0) - (if (g i).1.2 = c then 1 else 0) : ℂ)) • Ψ g := by
  rw [tAct_apply, Finset.sum_smul]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single (g i)]
  · simp [adP_Eab_self]
  · intro x _ hx
    simp [adP_Eab_self, hx]
  · simp

lemma single_mem_wtSub {R S k : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W] (actW : Mat R S →ₗ[ℂ] Module.End ℂ W)
    (g : Fin k → NC R S) (μ : Ix R S → ℚ) (w : W) (hw : w ∈ wtSub actW μ) :
    (Pi.single g w : (Fin k → NC R S) → W) ∈ wtSub (tAct k actW)
      (fun c => μ c + ∑ i, ((if (g i).1.1 = c then 1 else 0) - (if (g i).1.2 = c then 1 else 0))) := by
  rw [GlobalTheory.TensorHW.mem_wt] at hw ⊢
  intro c
  funext h
  rw [tAct_Eab_self_apply]
  by_cases hh : h = g
  · subst hh
    simp only [Pi.single_eq_same, Pi.smul_apply, hw c, ← add_smul]
    congr 1
    push_cast
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp
  · simp [hh]

theorem tAct_mem_iSup_wtSub (R S k : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W]
    (actW : Mat R S →ₗ[ℂ] Module.End ℂ W) (hW : ∀ w, w ∈ ⨆ μ : Ix R S → ℚ, wtSub actW μ)
    (Ψ : (Fin k → NC R S) → W) : Ψ ∈ ⨆ μ : Ix R S → ℚ, wtSub (tAct k actW) μ := by
  rw [← Finset.univ_sum_single Ψ]
  refine Submodule.sum_mem _ fun g _ => ?_
  refine Submodule.iSup_induction (motive := fun w => (Pi.single g w : (Fin k → NC R S) → W) ∈
    ⨆ μ : Ix R S → ℚ, wtSub (tAct k actW) μ) _ (hW (Ψ g)) ?_ ?_ ?_
  · intro μ w hw
    exact Submodule.mem_iSup_of_mem _ (single_mem_wtSub actW g μ w hw)
  · simp
  · intro x y hx hy
    rw [Pi.single_add]
    exact Submodule.add_mem _ hx hy

end GlobalTheory.SteepMult
