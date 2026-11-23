import Mathlib

namespace Formalism.FourierDecayAlt.P.FormNormSumIdentities

open Finset
open scoped ComplexConjugate InnerProductSpace

noncomputable section

section hilbert

variable {ι κ : Type*} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem inner_sum_smul (k : ι → ι → ℂ) (v : ι → H) (hv : ∀ p q, k p q = ⟪v p, v q⟫_ℂ) (J : Finset κ)
    (a : κ → ℂ) (P : κ → ι) :
    ⟪∑ j ∈ J, a j • v (P j), ∑ l ∈ J, a l • v (P l)⟫_ℂ =
      ∑ j ∈ J, ∑ l ∈ J, conj (a j) * a l * k (P j) (P l) := by
  rw [sum_inner]
  refine sum_congr rfl fun j _ => ?_
  rw [inner_smul_left, inner_sum, mul_sum]
  refine sum_congr rfl fun l _ => ?_
  rw [inner_smul_right, hv]
  ring

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem form_sum_conj (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (J : Finset κ) (a : κ → ℂ) (y : κ → V) :
    B (∑ j ∈ J, conj (a j) • y j) (∑ l ∈ J, conj (a l) • y l) =
      ∑ j ∈ J, ∑ l ∈ J, conj (a j) * a l * B (y j) (y l) := by
  rw [LinearMap.map_sum₂]
  refine sum_congr rfl fun j _ => ?_
  rw [map_smul, LinearMap.smul_apply, map_sum, smul_eq_mul, mul_sum]
  refine sum_congr rfl fun l _ => ?_
  rw [map_smulₛₗ, smul_eq_mul, Complex.conj_conj]
  ring

theorem norm_sq_sum_eq_form (k : ι → ι → ℂ) (v : ι → H) (hv : ∀ p q, k p q = ⟪v p, v q⟫_ℂ)
    (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (J : Finset κ) (a : κ → ℂ) (P : κ → ι) (y : κ → V)
    (hy : ∀ j ∈ J, ∀ l ∈ J, k (P j) (P l) = B (y j) (y l)) :
    ‖∑ j ∈ J, a j • v (P j)‖ ^ 2 = (B (∑ j ∈ J, conj (a j) • y j) (∑ j ∈ J, conj (a j) • y j)).re := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), inner_sum_smul k v hv, form_sum_conj, RCLike.re_to_complex]
  congr 1
  refine sum_congr rfl fun j hj => sum_congr rfl fun l hl => ?_
  rw [hy j hj l hl]

theorem norm_sum_le_of_form {W : Type*} [SeminormedAddCommGroup W] [Module ℂ W] (k : ι → ι → ℂ) (v : ι → H)
    (hv : ∀ p q, k p q = ⟪v p, v q⟫_ℂ) (B : W →ₗ[ℂ] W →ₗ⋆[ℂ] ℂ) (Cp : ℝ) (hCp : 0 ≤ Cp)
    (hB : ∀ x, (B x x).re ≤ (Cp * ‖x‖) ^ 2) (J : Finset κ) (a : κ → ℂ) (P : κ → ι) (y : κ → W)
    (hy : ∀ j ∈ J, ∀ l ∈ J, k (P j) (P l) = B (y j) (y l)) :
    ‖∑ j ∈ J, a j • v (P j)‖ ≤ Cp * ‖∑ j ∈ J, conj (a j) • y j‖ := by
  have h := norm_sq_sum_eq_form k v hv B J a P y hy
  have h2 := hB (∑ j ∈ J, conj (a j) • y j)
  rw [← h] at h2
  exact abs_le_of_sq_le_sq' h2 (by positivity) |>.2 |> fun h3 => by
    simpa [abs_of_nonneg (norm_nonneg _)] using (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h2

end hilbert

end

end Formalism.FourierDecayAlt.P.FormNormSumIdentities
