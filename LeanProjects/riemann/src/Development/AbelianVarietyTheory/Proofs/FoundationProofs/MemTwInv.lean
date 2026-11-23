import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRightInvRightTwisted

noncomputable section

namespace GlobalTheory.HeckeFamilyMatrices.CocBound

variable {G : Type} [Group G] {E : Type} [AddCommGroup E] [Module ℂ E]

def twInv (Γ : Subgroup G) (g : G) (A : E →ₗ[ℂ] E) : Submodule ℂ (G → E) :=
  GlobalTheory.TwistedInverseSubgroups.leftInvRightTwisted Γ g A

def cocyc (Γ : Subgroup G) (ρ : G → E →ₗ[ℂ] E) : Submodule ℂ (Γ → E) where
  carrier := {z | ∀ γ δ : Γ, z (γ * δ) = ρ (δ : G) (z γ) + z δ}
  add_mem' := by
    intro z z' h h' γ δ
    simp only [Pi.add_apply, h γ δ, h' γ δ, map_add]
    abel
  zero_mem' := fun _ _ => by simp
  smul_mem' := by
    intro c z h γ δ
    simp only [Pi.smul_apply, h γ δ, map_smul, smul_add]

def extn (Γ : Subgroup G) (ρ : G → E →ₗ[ℂ] E) (s : G) : Submodule ℂ (G → E) where
  carrier := {u | (∀ γ ∈ Γ, ∀ x, u (γ * x) - u x = ρ x (u γ - u 1)) ∧ ∀ x, u (x * s) = ρ s (u x)}
  add_mem' := by
    rintro f f' ⟨h1, h2⟩ ⟨h1', h2'⟩
    refine ⟨fun γ hγ x => ?_, fun x => by simp [h2, h2']⟩
    simp only [Pi.add_apply]
    rw [add_sub_add_comm, h1 γ hγ, h1' γ hγ, add_sub_add_comm, map_add]
  zero_mem' := ⟨fun _ _ _ => by simp, fun _ => by simp⟩
  smul_mem' := by
    rintro c f ⟨h1, h2⟩
    refine ⟨fun γ hγ x => ?_, fun x => by simp [h2]⟩
    simp only [Pi.smul_apply]
    rw [← smul_sub, h1 γ hγ, ← smul_sub, map_smul]

def relThree (Γ : Subgroup G) (ρ : G → E →ₗ[ℂ] E) (t : G) : Submodule ℂ (G → E) where
  carrier := {Φ | Φ ∈ twInv Γ (t ^ 3) (ρ (t ^ 3)) ∧
    ∀ x, ρ (t ^ 2) (Φ x) + ρ t (Φ (x * t)) + Φ (x * t ^ 2) = 0}
  add_mem' := by
    rintro f f' ⟨h1, h2⟩ ⟨h1', h2'⟩
    refine ⟨Submodule.add_mem _ h1 h1', fun x => ?_⟩
    simp only [Pi.add_apply, map_add]
    rw [← add_zero (0 : E)]
    nth_rewrite 1 [← h2 x]
    rw [← h2' x]
    abel
  zero_mem' := ⟨Submodule.zero_mem _, fun _ => by simp⟩
  smul_mem' := by
    rintro c f ⟨h1, h2⟩
    refine ⟨Submodule.smul_mem _ c h1, fun x => ?_⟩
    simp only [Pi.smul_apply, map_smul]
    rw [← smul_add, ← smul_add, h2, smul_zero]

end GlobalTheory.HeckeFamilyMatrices.CocBound
