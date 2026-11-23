import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsLeSup
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThK.IntV

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable (σ : E →ₐ[F] E) in

def autSub {n : ℕ} (Y : Spc F E n) : Submodule ℂ (UA σ Y.J → ℂ) where
  carrier := {f | Continuous f ∧ ∀ γ ∈ ratU σ Y.J, ∀ h, f (γ * h) = f h}
  add_mem' := by
    rintro f g ⟨hf, hf'⟩ ⟨hg, hg'⟩
    exact ⟨hf.add hg, fun γ hγ h => by simp only [Pi.add_apply, hf' γ hγ h, hg' γ hγ h]⟩
  zero_mem' := ⟨continuous_const, fun _ _ _ => rfl⟩
  smul_mem' := by
    rintro r f ⟨hf, hf'⟩
    exact ⟨continuous_const.mul hf, fun γ hγ h => by simp only [Pi.smul_apply, smul_eq_mul, hf' γ hγ h]⟩

variable (σ : E →ₐ[F] E) in

def IsHypPl {n n₁ : ℕ} (Y : Spc F E n) (Y₁ : Spc F E n₁) (H : Plane E n n₁) : Prop :=
  n = n₁ + 2 ∧ form σ Y.J H.x H.x = 0 ∧ form σ Y.J H.y H.y = 0 ∧ form σ Y.J H.x H.y = 1 ∧
    (∀ u, form σ Y.J (H.ι *ᵥ u) H.x = 0 ∧ form σ Y.J (H.ι *ᵥ u) H.y = 0) ∧ H.ιᵀ * Y.J * H.ι.map σ = Y₁.J ∧
    (∀ i j, σ (Y.J j i) = -Y.J i j) ∧ Y₁.J.det ≠ 0

end GlobalTheory.ThK.IntV

end
