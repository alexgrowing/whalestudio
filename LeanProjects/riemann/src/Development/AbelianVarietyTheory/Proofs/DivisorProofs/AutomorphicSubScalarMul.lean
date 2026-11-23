import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPurelyImaginaryElement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHermNDSmulSkewForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WordHolomorphicAndUniform
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability

open scoped ContDiff

namespace GlobalTheory.StdPar.AutLin

open GlobalTheory.WeakHolFamily

theorem comb_eq {G : Type} (φ₁ φ₂ : G → ℂ) (z : ℂ) : (fun g => φ₁ g - z * φ₂ g) = φ₁ + (-z) • φ₂ := by
  funext g; simp [sub_eq_add_neg]

theorem isAutOn_sub_smul : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E) (S : Finset (Fin r)) (K : Subgroup (GAd σ J))
    (φ₁ φ₂ : GAd σ J → ℂ) (z : ℂ), GlobalTheory.StdPar.IsAutOn σ J X Y S K φ₁ → GlobalTheory.StdPar.IsAutOn σ J X Y S K φ₂ →
      GlobalTheory.StdPar.IsAutOn σ J X Y S K (fun g => φ₁ g - z * φ₂ g) := by
  intro F E _ _ _ _ _ σ n J r X Y S K φ₁ φ₂ z h₁ h₂
  have s₁ : SmoothLines σ J φ₁ := h₁.smooth
  have s₂ : SmoothLines σ J ((-z) • φ₂) := smoothLines_smul (-z) h₂.smooth
  have hfold : ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) →
      l.foldr lineDer (fun g => φ₁ g - z * φ₂ g) = fun g => l.foldr lineDer φ₁ g - z * l.foldr lineDer φ₂ g := by
    intro l hl
    rw [comb_eq, foldr_add s₁ s₂ l hl, foldr_smul, comb_eq]
  refine ⟨fun u hu g => by simp only [h₁.leftN u hu g, h₂.leftN u hu g],
    fun γ hγ hγ' g => by simp only [h₁.leftM γ hγ hγ' g, h₂.leftM γ hγ hγ' g], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨U₁, o₁, e₁⟩ := h₁.level
    obtain ⟨U₂, o₂, e₂⟩ := h₂.level
    exact ⟨U₁ ⊓ U₂, o₁.inter o₂, fun k hk hf g => by
      simp only [e₁ k hk.1 hf g, e₂ k hk.2 hf g]⟩
  · exact h₁.cont.sub (continuous_const.mul h₂.cont)
  · have : SmoothLines σ J (φ₁ + (-z) • φ₂) := smoothLines_add s₁ s₂
    rw [comb_eq]; exact this
  · obtain ⟨N₁, g₁⟩ := h₁.growth
    obtain ⟨N₂, g₂⟩ := h₂.growth
    refine ⟨max N₁ N₂, fun l hl => ?_⟩
    obtain ⟨C₁, c₁⟩ := g₁ l hl
    obtain ⟨C₂, c₂⟩ := g₂ l hl
    refine ⟨max C₁ 0 + ‖z‖ * max C₂ 0, fun g => ?_⟩
    rw [hfold l hl]
    have hh : (1 : ℝ) ≤ (height σ J g : ℝ) := by exact_mod_cast one_le_height σ J g
    have p₁ : (height σ J g : ℝ) ^ N₁ ≤ (height σ J g : ℝ) ^ max N₁ N₂ := pow_le_pow_right₀ hh (le_max_left _ _)
    have p₂ : (height σ J g : ℝ) ^ N₂ ≤ (height σ J g : ℝ) ^ max N₁ N₂ := pow_le_pow_right₀ hh (le_max_right _ _)
    have q₁ : (0 : ℝ) ≤ (height σ J g : ℝ) ^ N₁ := by positivity
    have q₂ : (0 : ℝ) ≤ (height σ J g : ℝ) ^ N₂ := by positivity
    have a₁ : ‖l.foldr lineDer φ₁ g‖ ≤ max C₁ 0 * (height σ J g : ℝ) ^ max N₁ N₂ :=
      (c₁ g).trans ((mul_le_mul_of_nonneg_right (le_max_left _ _) q₁).trans
        (mul_le_mul_of_nonneg_left p₁ (le_max_right _ _)))
    have a₂ : ‖l.foldr lineDer φ₂ g‖ ≤ max C₂ 0 * (height σ J g : ℝ) ^ max N₁ N₂ :=
      (c₂ g).trans ((mul_le_mul_of_nonneg_right (le_max_left _ _) q₂).trans
        (mul_le_mul_of_nonneg_left p₂ (le_max_right _ _)))
    calc ‖l.foldr lineDer φ₁ g - z * l.foldr lineDer φ₂ g‖
        ≤ ‖l.foldr lineDer φ₁ g‖ + ‖z‖ * ‖l.foldr lineDer φ₂ g‖ := by
          rw [← norm_mul]; exact norm_sub_le _ _
      _ ≤ max C₁ 0 * (height σ J g : ℝ) ^ max N₁ N₂ + ‖z‖ * (max C₂ 0 * (height σ J g : ℝ) ^ max N₁ N₂) :=
          add_le_add a₁ (mul_le_mul_of_nonneg_left a₂ (norm_nonneg _))
      _ = (max C₁ 0 + ‖z‖ * max C₂ 0) * (height σ J g : ℝ) ^ max N₁ N₂ := by ring
  · have := h₁.kfin
    have := h₂.kfin
    refine Submodule.finiteDimensional_of_le
      (S₂ := Submodule.span ℂ (Set.range fun k : K => fun g => φ₁ (g * k)) ⊔
        Submodule.span ℂ (Set.range fun k : K => fun g => φ₂ (g * k))) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    have e : (fun g => φ₁ (g * k) - z * φ₂ (g * k)) = (fun g => φ₁ (g * k)) - z • fun g => φ₂ (g * k) := by
      funext g; simp
    show (fun g => φ₁ (g * k) - z * φ₂ (g * k)) ∈ _
    rw [e]
    exact sub_mem (Submodule.mem_sup_left (Submodule.subset_span ⟨k, rfl⟩))
      (Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)))
  · have := h₁.zfin
    have := h₂.zfin
    refine Submodule.finiteDimensional_of_le
      (S₂ := Submodule.span ℂ {f | ∃ z', IsCentral σ J z' ∧ f = dop z' φ₁} ⊔
        Submodule.span ℂ {f | ∃ z', IsCentral σ J z' ∧ f = dop z' φ₂}) (Submodule.span_le.2 ?_)
    rintro _ ⟨z', hz', rfl⟩
    have e : dop z' (fun g => φ₁ g - z * φ₂ g) = dop z' φ₁ - z • dop z' φ₂ := by
      funext g
      simp only [dop, Finsupp.sum, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun l hl => ?_
      rw [hfold l (hz'.1 l hl)]
      ring
    rw [e]
    exact sub_mem (Submodule.mem_sup_left (Submodule.subset_span ⟨z', hz', rfl⟩))
      (Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.subset_span ⟨z', hz', rfl⟩)))

end GlobalTheory.StdPar.AutLin
