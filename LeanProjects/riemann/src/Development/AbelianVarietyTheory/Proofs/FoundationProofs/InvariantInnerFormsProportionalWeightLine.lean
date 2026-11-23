import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.HeckeCharacterParameters
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SameBlockOfPosC
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

namespace GlobalTheory.FockForm

theorem act_of_mem_wtSub {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {act : Mat p q →ₗ[ℂ] Module.End ℂ V} {μ : Ix p q → ℚ} {x : V} (h : x ∈ wtSub act μ)
    (a : Ix p q) : act (Eab a a) x = ((μ a : ℚ) : ℂ) • x := by
  have := (Submodule.mem_iInf _).1 h a
  simpa [LinearMap.mem_ker, sub_eq_zero] using this

theorem form_eq_zero {p q : ℕ} (M : GKMod p q) (D : M.V → M.V → ℂ)
    (hadd₁ : ∀ x x' y, D (x + x') y = D x y + D x' y)
    (hsmul₁ : ∀ (c : ℂ) x y, D (c • x) y = star c * D x y)
    (hadd₂ : ∀ x y y', D x (y + y') = D x y + D x y')
    (hsmul₂ : ∀ (c : ℂ) x y, D x (c • y) = c * D x y)
    (hinv : ∀ Z x y, D (M.act Z x) y = D x (M.act (adjZ Z) y))
    (μ : Ix p q → ℚ) (v : M.V) (hv : v ∈ wtSub M.act μ)
    (hline : ∀ x ∈ wtSub M.act μ, ∃ c : ℂ, x = c • v) (hgen : genSub M.act {v} = ⊤)
    (hvv : D v v = 0) : ∀ x y, D x y = 0 := by
  have hv0 : ∀ y, D v y = 0 := by
    intro y
    refine Submodule.iSup_induction (motive := fun y => D v y = 0) _ (M.wts y) ?_ ?_ ?_
    · intro ν y hy
      by_cases hν : ν = μ
      · subst hν
        obtain ⟨c, rfl⟩ := hline y hy
        rw [hsmul₂, hvv, mul_zero]
      · obtain ⟨a, ha⟩ := Function.ne_iff.1 hν
        have h := hinv (Eab a a) v y
        rw [GlobalTheory.FockTensor.adjZ_Eab, GlobalTheory.FockTensor.sgnIx_mul_self, one_smul,
          act_of_mem_wtSub hv, act_of_mem_wtSub hy, hsmul₁, hsmul₂] at h
        have hs : star ((μ a : ℚ) : ℂ) = ((μ a : ℚ) : ℂ) := by simp
        rw [hs] at h
        have hne : ((μ a : ℚ) : ℂ) - ((ν a : ℚ) : ℂ) ≠ 0 := by
          rw [sub_ne_zero]; exact_mod_cast ha.symm
        have : (((μ a : ℚ) : ℂ) - ((ν a : ℚ) : ℂ)) * D v y = 0 := by linear_combination h
        exact (mul_eq_zero.1 this).resolve_left hne
    · have := hsmul₂ 0 v 0
      simpa using this
    · intro y y' h h'
      rw [hadd₂, h, h', add_zero]
  let N : Submodule ℂ M.V :=
    { carrier := {x | ∀ y, D x y = 0}
      add_mem' := fun {x x'} h h' y => by rw [hadd₁, h y, h' y, add_zero]
      zero_mem' := fun y => by simpa using hsmul₁ 0 0 y
      smul_mem' := fun c x h y => by rw [hsmul₁, h y, mul_zero] }
  have hN : genSub M.act {v} ≤ N := by
    apply sInf_le
    refine ⟨?_, ?_⟩
    · intro x hx
      rw [Set.mem_singleton_iff.1 hx]
      exact hv0
    · intro Z x hx y
      rw [hinv]
      exact hx _
  intro x y
  exact hN (hgen ▸ Submodule.mem_top) y

theorem inner_eq_mul : ∀ (p q : ℕ) (M : GKMod p q) (H₁ : Type) [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (H₂ : Type) [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] (j : M.V →ₗ[ℂ] H₁) (E₁ E₂ : M.V →ₗ[ℂ] H₂), (∀ Z x y, inner ℂ (j (M.act Z x)) (j y) = inner ℂ (j x) (j (M.act (adjZ Z) y))) → (∀ Z x y, inner ℂ (E₁ (M.act Z x)) (E₂ y) = inner ℂ (E₁ x) (E₂ (M.act (adjZ Z) y))) → ∀ (μ : Ix p q → ℚ) (v : M.V), v ∈ wtSub M.act μ → (∀ x ∈ wtSub M.act μ, ∃ c : ℂ, x = c • v) → genSub M.act {v} = ⊤ → ‖j v‖ = 1 → ∀ x y, inner ℂ (E₁ x) (E₂ y) = inner ℂ (E₁ v) (E₂ v) * inner ℂ (j x) (j y) := by
  intro p q M H₁ _ _ H₂ _ _ j E₁ E₂ hj hE μ v hv hline hgen hnorm x y
  have := form_eq_zero M
    (fun x y => inner ℂ (E₁ x) (E₂ y) - inner ℂ (E₁ v) (E₂ v) * inner ℂ (j x) (j y))
    (fun x x' y => by simp only [map_add, inner_add_left]; ring)
    (fun c x y => by simp only [map_smul, inner_smul_left, starRingEnd_apply]; ring)
    (fun x y y' => by simp only [map_add, inner_add_right]; ring)
    (fun c x y => by simp only [map_smul, inner_smul_right]; ring)
    (fun Z x y => by simp only [hj, hE])
    μ v hv hline hgen (by simp [inner_self_eq_norm_sq_to_K, hnorm]) x y
  exact sub_eq_zero.1 this

end GlobalTheory.FockForm
