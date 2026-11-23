import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WordAppend
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical
open GlobalTheory.ArchDecay

namespace GlobalTheory.ArchDecay

theorem onePlusNormPow_le_sum_linearForm_pow : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (N : ℕ), ∃ (K : ℕ) (l : Fin K → (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ) (C : ℝ), (∀ j, ‖l j‖ ≤ 1) ∧ ∀ y, (1 + ‖y‖) ^ N ≤ C * (1 + ∑ j, |l j y| ^ N) := by
  intro F _ _ κ _ N
  let b := Module.finBasis ℝ (κ → mixedEmbedding.mixedSpace F)
  let K := Module.finrank ℝ (κ → mixedEmbedding.mixedSpace F)
  let c : Fin K → (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ :=
    fun j => LinearMap.toContinuousLinearMap (b.coord j)
  let w : Fin K → ℝ := fun j => (1 + ‖c j‖) * ‖b j‖
  have hw : ∀ j, 0 ≤ w j := fun j => by positivity
  let W : ℝ := 1 + ∑ j, w j
  have hW1 : 1 ≤ W := by
    have := Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => hw j); simp only [W]; linarith
  have hwW : ∀ j, w j ≤ W := fun j => by
    have := Finset.single_le_sum (f := w) (fun j _ => hw j) (Finset.mem_univ j)
    simp only [W]; linarith
  let l : Fin K → (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ := fun j => (1 + ‖c j‖)⁻¹ • c j
  have hl : ∀ j, ‖l j‖ ≤ 1 := fun j => by
    have h0 : 0 < 1 + ‖c j‖ := by positivity
    simp only [l, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos h0]
    rw [inv_mul_le_iff₀ h0]; linarith
  have hlw : ∀ j y, |l j y| * w j = |b.repr y j| * ‖b j‖ := fun j y => by
    have h0 : 0 < 1 + ‖c j‖ := by positivity
    simp only [l, w, c, ContinuousLinearMap.smul_apply, LinearMap.coe_toContinuousLinearMap',
      Module.Basis.coord_apply, smul_eq_mul, abs_mul, abs_inv, abs_of_pos h0]
    field_simp
  have hnorm : ∀ y, ‖y‖ ≤ ∑ j, |l j y| * w j := fun y => by
    calc ‖y‖ = ‖∑ j, b.repr y j • b j‖ := by rw [b.sum_repr y]
      _ ≤ ∑ j, ‖b.repr y j • b j‖ := norm_sum_le _ _
      _ = ∑ j, |l j y| * w j := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hlw, norm_smul, Real.norm_eq_abs]
  refine ⟨K, l, ((K : ℝ) + 1) ^ N * W ^ N, hl, fun y => ?_⟩
  have hS : 0 ≤ ∑ j, |l j y| ^ N := Finset.sum_nonneg fun j _ => by positivity
  rcases N with _ | n
  · simp only [pow_zero, one_mul]
    have : (0:ℝ) ≤ ∑ _x : Fin K, (1:ℝ) := by positivity
    linarith
  let f : Option (Fin K) → ℝ := fun o => Option.elim o 1 fun j => |l j y| * w j
  have hf : ∀ o ∈ (Finset.univ : Finset (Option (Fin K))), 0 ≤ f o := by
    intro o _; cases o with
    | none => simp [f]
    | some j => simp only [f, Option.elim_some]; exact mul_nonneg (abs_nonneg _) (hw j)
  have h1 : 1 + ‖y‖ ≤ ∑ o, f o := by
    rw [Fintype.sum_option]; simp only [f, Option.elim_none, Option.elim_some]
    linarith [hnorm y]
  have h2 := pow_sum_le_card_mul_sum_pow hf n
  rw [Finset.card_univ, Fintype.card_option, Fintype.card_fin, Fintype.sum_option] at h2
  simp only [f, Option.elim_none, Option.elim_some, one_pow] at h2
  have h3 : ∑ j, (|l j y| * w j) ^ (n + 1) ≤ W ^ (n + 1) * ∑ j, |l j y| ^ (n + 1) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [mul_pow, mul_comm]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (hw j) (hwW j) _) (by positivity)
  have hW : 1 ≤ W ^ (n + 1) := one_le_pow₀ hW1
  have hK : ((K : ℝ) + 1) ^ n ≤ ((K : ℝ) + 1) ^ (n + 1) :=
    pow_le_pow_right₀ (by linarith [(K.cast_nonneg : (0:ℝ) ≤ K)]) (Nat.le_succ n)
  have hKn : 0 ≤ ((K : ℝ) + 1) ^ n := by positivity
  calc (1 + ‖y‖) ^ (n + 1) ≤ (∑ o, f o) ^ (n + 1) :=
        pow_le_pow_left₀ (by positivity) h1 _
    _ ≤ ((K : ℝ) + 1) ^ n * (1 + ∑ j, (|l j y| * w j) ^ (n + 1)) := by
        rw [Fintype.sum_option]; simpa [f] using h2
    _ ≤ ((K : ℝ) + 1) ^ n * (W ^ (n + 1) * (1 + ∑ j, |l j y| ^ (n + 1))) := by
        gcongr; nlinarith
    _ ≤ ((K : ℝ) + 1) ^ (n + 1) * W ^ (n + 1) * (1 + ∑ j, |l j y| ^ (n + 1)) := by
        rw [← mul_assoc]; gcongr

end GlobalTheory.ArchDecay
