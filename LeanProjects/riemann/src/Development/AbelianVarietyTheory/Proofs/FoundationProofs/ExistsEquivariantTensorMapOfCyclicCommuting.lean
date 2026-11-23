import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.HeckeCharacterParameters
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SameBlockOfPosC
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

namespace GlobalTheory.FockBilin

theorem gen_ind {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (x₀ : V) (h : genSub act {x₀} = ⊤)
    (N : Submodule ℂ V) (h0 : x₀ ∈ N) (hs : ∀ Z, ∀ y ∈ N, act Z y ∈ N) (x : V) : x ∈ N := by
  have hle : genSub act {x₀} ≤ N := sInf_le ⟨by simpa using h0, hs⟩
  rw [h] at hle
  exact hle Submodule.mem_top

theorem uniq {p q : ℕ} {U V : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ U) (a : Mat p q →ₗ[ℂ] Module.End ℂ V) (x₀ : U)
    (h : genSub act {x₀} = ⊤) (f g : U →ₗ[ℂ] V)
    (hf : ∀ Z x, f (act Z x) = a Z (f x)) (hg : ∀ Z x, g (act Z x) = a Z (g x))
    (h0 : f x₀ = g x₀) : f = g := by
  ext x
  have := gen_ind act x₀ h (LinearMap.eqLocus f g) h0 (fun Z y hy => by
    rw [LinearMap.mem_eqLocus] at hy ⊢
    rw [hf, hg, hy]) x
  exact this

theorem exists_bilin : ∀ (p q r s : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (a₁ : Mat p q →ₗ[ℂ] Module.End ℂ V) (a₂ : Mat r s →ₗ[ℂ] Module.End ℂ V), (∀ Y Z, a₁ Y * a₂ Z = a₂ Z * a₁ Y) → ∀ (M₁ : GKMod p q) (M₂ : GKMod r s) (i₁ : M₁.V →ₗ[ℂ] V) (i₂ : M₂.V →ₗ[ℂ] V), (∀ Z x, i₁ (M₁.act Z x) = a₁ Z (i₁ x)) → (∀ Z y, i₂ (M₂.act Z y) = a₂ Z (i₂ y)) → ∀ (x₀ : M₁.V) (y₀ : M₂.V), genSub M₁.act {x₀} = ⊤ → genSub M₂.act {y₀} = ⊤ → i₁ x₀ = i₂ y₀ → ∃ I : M₁.V ⊗[ℂ] M₂.V →ₗ[ℂ] V, (∀ Z x y, a₁ Z (I (x ⊗ₜ y)) = I (M₁.act Z x ⊗ₜ y)) ∧ (∀ Z x y, a₂ Z (I (x ⊗ₜ y)) = I (x ⊗ₜ M₂.act Z y)) ∧ (∀ x, I (x ⊗ₜ y₀) = i₁ x) ∧ ∀ y, I (x₀ ⊗ₜ y) = i₂ y := by
  intro p q r s V _ _ a₁ a₂ hc M₁ M₂ i₁ i₂ h₁ h₂ x₀ y₀ g₁ g₂ h0
  have hc' : ∀ Y Z v, a₁ Y (a₂ Z v) = a₂ Z (a₁ Y v) := fun Y Z v =>
    LinearMap.congr_fun (hc Y Z) v
  let N : Submodule ℂ M₂.V :=
    { carrier := {y | ∃ f : M₁.V →ₗ[ℂ] V, (∀ Z x, f (M₁.act Z x) = a₁ Z (f x)) ∧ f x₀ = i₂ y}
      add_mem' := by
        rintro y y' ⟨f, hf, e⟩ ⟨g, hg, e'⟩
        exact ⟨f + g, fun Z x => by simp [hf, hg], by simp [e, e']⟩
      zero_mem' := ⟨0, by simp, by simp⟩
      smul_mem' := by
        rintro c y ⟨f, hf, e⟩
        exact ⟨c • f, fun Z x => by simp [hf], by simp [e]⟩ }
  have hN : ∀ y, ∃ f : M₁.V →ₗ[ℂ] V, (∀ Z x, f (M₁.act Z x) = a₁ Z (f x)) ∧ f x₀ = i₂ y := by
    intro y
    refine gen_ind M₂.act y₀ g₂ N ⟨i₁, h₁, h0⟩ ?_ y
    rintro Z y ⟨f, hf, e⟩
    exact ⟨a₂ Z ∘ₗ f, fun Y x => by simp [hf, hc'], by simp [e, h₂]⟩
  choose F hF hF0 using hN
  have u := uniq M₁.act a₁ x₀ g₁
  have hadd : ∀ y y', F (y + y') = F y + F y' := fun y y' =>
    u _ _ (hF _) (fun Z x => by simp [hF]) (by simp [hF0])
  have hsmul : ∀ (c : ℂ) y, F (c • y) = c • F y := fun c y =>
    u _ _ (hF _) (fun Z x => by simp [hF]) (by simp [hF0])
  have hact : ∀ Z y, F (M₂.act Z y) = a₂ Z ∘ₗ F y := fun Z y =>
    u _ _ (hF _) (fun Y x => by simp [hF, hc']) (by simp [hF0, h₂])
  have hy0 : F y₀ = i₁ := u _ _ (hF _) h₁ (by rw [hF0, h0])
  let G : M₂.V →ₗ[ℂ] M₁.V →ₗ[ℂ] V := { toFun := F, map_add' := hadd, map_smul' := hsmul }
  have hG : ∀ x y, TensorProduct.lift G.flip (x ⊗ₜ y) = F y x := fun x y => by
    simp [G]
  refine ⟨TensorProduct.lift G.flip, ?_, ?_, ?_, ?_⟩
  · intro Z x y; rw [hG, hG, hF]
  · intro Z x y; rw [hG, hG, hact]; rfl
  · intro x; rw [hG, hy0]
  · intro y; rw [hG, hF0]

end GlobalTheory.FockBilin
