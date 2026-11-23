import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLatBasisZero

set_option autoImplicit false

noncomputable section

open Topology

namespace GlobalTheory.ShFam.Hor.LogCh

open Topology in
set_option autoImplicit false in
private theorem exists_pos_int_combination_eq_zero_near_of_linearIndependent {g r : ℕ} {l₁ : Fin r → Fin g → ℂ}
    (hl : LinearIndependent ℝ l₁) :
    ∃ δ > 0, ∀ l : Fin r → Fin g → ℂ, ‖l - l₁‖ < δ → ∀ c : Fin r → ℤ,
      ‖∑ j, c j • l j‖ < δ → c = 0 := by
  set L : (Fin r → ℝ) →ₗ[ℝ] (Fin g → ℂ) := Fintype.linearCombination ℝ l₁ with hL
  have hLapp : ∀ x, L x = ∑ j, x j • l₁ j := fun x => by
    simp [hL, Fintype.linearCombination_apply]
  have hker : LinearMap.ker L = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro x hx
    exact funext (Fintype.linearIndependent_iff.1 hl x (by rw [← hLapp]; exact hx))
  obtain ⟨K, -, hK⟩ := L.exists_antilipschitzWith hker
  set k : ℝ := (K : ℝ) + 1 with hk
  have hk0 : 0 < k := by positivity
  have hbound : ∀ x, ‖x‖ ≤ k * ‖L x‖ := fun x => by
    have h := hK.le_mul_dist x 0
    simp only [map_zero, dist_zero_right] at h
    nlinarith [norm_nonneg (L x)]
  refine ⟨1 / (2 * k * ((r : ℝ) + 1)), by positivity, fun l hl c hc => ?_⟩
  set δ : ℝ := 1 / (2 * k * ((r : ℝ) + 1)) with hδ
  set x : Fin r → ℝ := fun j => (c j : ℝ) with hx
  have hcx : ∑ j, c j • l j = ∑ j, x j • l j := by
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [hx, Int.cast_smul_eq_zsmul]
  have hsplit : L x = ∑ j, x j • l j - ∑ j, x j • (l j - l₁ j) := by
    rw [hLapp]
    simp [smul_sub, Finset.sum_sub_distrib]
  have hsum : ‖∑ j, x j • (l j - l₁ j)‖ ≤ r * (‖x‖ * ‖l - l₁‖) := by
    calc ‖∑ j, x j • (l j - l₁ j)‖ ≤ ∑ j, ‖x j • (l j - l₁ j)‖ := norm_sum_le _ _
      _ ≤ ∑ _j : Fin r, ‖x‖ * ‖l - l₁‖ := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [norm_smul]
        exact mul_le_mul (norm_le_pi_norm x j) (by simpa using norm_le_pi_norm (l - l₁) j)
          (norm_nonneg _) (norm_nonneg _)
      _ = r * (‖x‖ * ‖l - l₁‖) := by simp
  have hLx : ‖L x‖ < δ + r * (‖x‖ * δ) := by
    rw [hsplit]
    calc ‖∑ j, x j • l j - ∑ j, x j • (l j - l₁ j)‖
        ≤ ‖∑ j, x j • l j‖ + ‖∑ j, x j • (l j - l₁ j)‖ := norm_sub_le _ _
      _ < δ + r * (‖x‖ * δ) := by
        have h1 : ‖∑ j, x j • l j‖ < δ := by rw [← hcx]; exact hc
        have h2 : r * (‖x‖ * ‖l - l₁‖) ≤ r * (‖x‖ * δ) := by
          gcongr
        linarith
  have hkδ : k * δ * ((r : ℝ) + 1) = 1 / 2 := by
    rw [hδ]; field_simp
  have hxlt : ‖x‖ < 1 := by
    have hb := hbound x
    have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    have hxn := norm_nonneg x
    have hδ0 : 0 < δ := by positivity
    have : ‖x‖ < k * δ + k * δ * r * ‖x‖ := by
      calc ‖x‖ ≤ k * ‖L x‖ := hb
        _ < k * (δ + r * (‖x‖ * δ)) := mul_lt_mul_of_pos_left hLx hk0
        _ = k * δ + k * δ * r * ‖x‖ := by ring
    have hkδ0 : 0 < k * δ := mul_pos hk0 hδ0
    have hkδ' : k * δ * r + k * δ = 1 / 2 := by rw [← hkδ]; ring
    have ha : k * δ * r ≤ 1 / 2 := by linarith
    have ha2 : k * δ ≤ 1 / 2 := by nlinarith
    have hm : k * δ * r * ‖x‖ ≤ 1 / 2 * ‖x‖ := mul_le_mul_of_nonneg_right ha hxn
    linarith
  funext j
  have hj : ‖x j‖ < 1 := lt_of_le_of_lt (norm_le_pi_norm x j) hxlt
  have hj' : |(c j : ℝ)| < 1 := by simpa [hx] using hj
  have : |c j| < 1 := by exact_mod_cast hj'
  simpa using Int.abs_lt_one_iff.1 this

open Topology in
set_option autoImplicit false in

theorem _root_.GlobalTheory.ShFam.Hor.LogCh.exists_const_coords (n g r : ℕ) (B : Set (Fin n → ℂ))
    (K : (Fin n → ℂ) → Set (Fin g → ℂ))
    (lam : (Fin n → ℂ) → Fin r → Fin g → ℂ) (ζ : (Fin n → ℂ) → Fin g → ℂ) (b₀ : Fin n → ℂ)
    (hB : IsPreconnected B) (hlam : ContinuousOn lam B) (hζ : ContinuousOn ζ B)
    (hbas : ∀ b ∈ B, _root_.GlobalTheory.ShFam.Hor.LogCh.IsLatBasis (K b) (lam b)) (hmem : ∀ b ∈ B, ζ b ∈ K b)
    (hb₀ : b₀ ∈ B) :
    ∃ m : Fin r → ℤ, ∀ b ∈ B, ζ b = ∑ j, m j • lam b j := by
  classical
  have hex : ∀ b ∈ B, ∃ m : Fin r → ℤ, ζ b = ∑ j, m j • lam b j :=
    fun b hb => ((hbas b hb).2 (ζ b)).1 (hmem b hb)
  let F : (Fin n → ℂ) → Fin r → ℤ := fun b => if hb : b ∈ B then (hex b hb).choose else 0
  have hF : ∀ b ∈ B, ζ b = ∑ j, F b j • lam b j := by
    intro b hb
    simp only [F, dif_pos hb]
    exact (hex b hb).choose_spec
  have hloc : ∀ b₁ ∈ B, ∀ᶠ b in 𝓝[B] b₁, F b = F b₁ := by
    intro b₁ hb₁
    obtain ⟨δ, hδ, hkey⟩ := exists_pos_int_combination_eq_zero_near_of_linearIndependent (hbas b₁ hb₁).1
    have h1 : ∀ᶠ b in 𝓝[B] b₁, ‖lam b - lam b₁‖ < δ := by
      have hc : ContinuousWithinAt (fun b => ‖lam b - lam b₁‖) B b₁ :=
        ((hlam b₁ hb₁).sub continuousWithinAt_const).norm
      exact hc.eventually (eventually_lt_nhds (by simpa using hδ))
    have hcomb : Continuous (fun l : Fin r → Fin g → ℂ => ∑ j, F b₁ j • l j) :=
      continuous_finset_sum _ fun j _ => (continuous_apply j).const_smul (F b₁ j)
    have h2 : ∀ᶠ b in 𝓝[B] b₁, ‖ζ b - ∑ j, F b₁ j • lam b j‖ < δ := by
      have hc : ContinuousWithinAt (fun b => ‖ζ b - ∑ j, F b₁ j • lam b j‖) B b₁ :=
        ((hζ b₁ hb₁).sub (hcomb.continuousAt.comp_continuousWithinAt (hlam b₁ hb₁))).norm
      refine hc.eventually (eventually_lt_nhds ?_)
      show ‖ζ b₁ - ∑ j, F b₁ j • lam b₁ j‖ < δ
      rw [← hF b₁ hb₁, sub_self, norm_zero]
      exact hδ
    filter_upwards [h1, h2, self_mem_nhdsWithin] with b hb1 hb2 hbB
    have hdiff : ∑ j, (F b - F b₁) j • lam b j = ζ b - ∑ j, F b₁ j • lam b j := by
      rw [hF b hbB]
      simp [sub_smul, Finset.sum_sub_distrib]
    exact sub_eq_zero.1 (hkey (lam b) hb1 (F b - F b₁) (by rw [hdiff]; exact hb2))
  have hcont : ContinuousOn F B := fun b₁ hb₁ =>
    continuousWithinAt_const.congr_of_eventuallyEq (hloc b₁ hb₁) rfl
  refine ⟨F b₀, fun b hb => ?_⟩
  rw [← hB.constant hcont hb hb₀]
  exact hF b hb

end GlobalTheory.ShFam.Hor.LogCh
