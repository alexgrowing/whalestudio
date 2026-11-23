import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.ExtendByZero

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {κ₁ κ : Type} [Fintype κ₁] [Fintype κ]

theorem extend_zero_add {j : κ₁ → κ} (hj : Function.Injective j) (y z : κ₁ → V) :
    Function.extend j (y + z) (0 : κ → V) = Function.extend j y 0 + Function.extend j z 0 := by
  ext i
  by_cases h : ∃ a, j a = i
  · obtain ⟨a, rfl⟩ := h
    simp [hj.extend_apply]
  · simp [Function.extend_apply' _ _ _ h]

theorem extend_zero_smul {j : κ₁ → κ} (hj : Function.Injective j) (c : ℝ) (y : κ₁ → V) :
    Function.extend j (c • y) (0 : κ → V) = c • Function.extend j y 0 := by
  ext i
  by_cases h : ∃ a, j a = i
  · obtain ⟨a, rfl⟩ := h
    simp [hj.extend_apply]
  · simp [Function.extend_apply' _ _ _ h]

def clm {j : κ₁ → κ} (hj : Function.Injective j) : (κ₁ → V) →L[ℝ] (κ → V) where
  toFun y := Function.extend j y 0
  map_add' := extend_zero_add hj
  map_smul' := extend_zero_smul hj
  cont := by
    refine continuous_pi fun i => ?_
    by_cases h : ∃ a, j a = i
    · obtain ⟨a, rfl⟩ := h
      simp only [hj.extend_apply]
      exact continuous_apply a
    · simp only [Function.extend_apply' _ _ _ h]
      exact continuous_const

theorem clm_apply {j : κ₁ → κ} (hj : Function.Injective j) (y : κ₁ → V) : clm hj y = Function.extend j y 0 := rfl

theorem norm_le_norm_clm {j : κ₁ → κ} (hj : Function.Injective j) (y : κ₁ → V) : ‖y‖ ≤ ‖clm hj y‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun a => ?_
  have h : clm hj y (j a) = y a := by rw [clm_apply, hj.extend_apply]
  rw [← h]
  exact norm_le_pi_norm (clm hj y) (j a)

end GlobalTheory.ExtendByZero

namespace GlobalTheory.RestrS

open scoped Classical in

theorem exists_restr : ∀ (F : Type) [Field F] [NumberField F] {κ₁ κ : Type} [Fintype κ₁] [Fintype κ] (j : κ₁ → κ), Function.Injective j →
    ∃ R : SInf F κ →L[ℂ] SInf F κ₁, ∀ f y, R f y = f (Function.extend j y 0) := by
  intro F _ _ κ₁ κ _ _ j hj
  refine ⟨SchwartzMap.compCLM ℂ (GlobalTheory.ExtendByZero.clm (V := mixedEmbedding.mixedSpace F) hj).hasTemperateGrowth
    ⟨1, 1, fun y => ?_⟩, fun f y => rfl⟩
  have := GlobalTheory.ExtendByZero.norm_le_norm_clm (V := mixedEmbedding.mixedSpace F) hj y
  simp only [pow_one, one_mul]
  linarith

end GlobalTheory.RestrS
