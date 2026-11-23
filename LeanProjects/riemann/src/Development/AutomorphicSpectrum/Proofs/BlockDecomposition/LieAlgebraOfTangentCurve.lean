import Mathlib
import Formalism.UnipotentAdelicQuotients.SmComplete
open SmoothVectors Filter Topology
open scoped ContDiff Matrix.Norms.Elementwise

namespace GlobalTheory.CompanionTheory.SmTangent

section Abstract

variable {A : Type*} [NormedRing A]

theorem norm_pow_le_pow_of_le (h1 : ‖(1 : A)‖ ≤ 1) {b : A} {C : ℝ} (hC : 1 ≤ C) (hb : ‖b‖ ≤ C) (k : ℕ) :
    ‖b ^ k‖ ≤ C ^ k := by
  induction k with
  | zero => simpa using h1
  | succ k ih =>
    rw [pow_succ, pow_succ]
    calc ‖b ^ k * b‖ ≤ ‖b ^ k‖ * ‖b‖ := norm_mul_le _ _
      _ ≤ C ^ k * C := by
        gcongr

theorem norm_pow_sub_pow_le (h1 : ‖(1 : A)‖ ≤ 1) {a b : A} {C : ℝ} (hC : 1 ≤ C) (ha : ‖a‖ ≤ C)
    (hb : ‖b‖ ≤ C) (k : ℕ) : ‖a ^ k - b ^ k‖ ≤ k * C ^ k * ‖a - b‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : a ^ (k + 1) - b ^ (k + 1) = a * (a ^ k - b ^ k) + (a - b) * b ^ k := by
      rw [pow_succ', pow_succ']
      noncomm_ring
    have hC0 : 0 ≤ C := by linarith
    have hCk : 1 ≤ C ^ k := one_le_pow₀ hC
    have hd : 0 ≤ ‖a - b‖ := norm_nonneg _
    have t1 : ‖a * (a ^ k - b ^ k)‖ ≤ C * (k * C ^ k * ‖a - b‖) :=
      (norm_mul_le _ _).trans (by gcongr)
    have t2 : ‖(a - b) * b ^ k‖ ≤ ‖a - b‖ * C ^ k :=
      (norm_mul_le _ _).trans (by gcongr; exact norm_pow_le_pow_of_le h1 hC hb k)
    have t3 : ‖a - b‖ * C ^ k ≤ ‖a - b‖ * C ^ (k + 1) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hC (Nat.le_succ k)) hd
    rw [e]
    calc ‖a * (a ^ k - b ^ k) + (a - b) * b ^ k‖
        ≤ ‖a * (a ^ k - b ^ k)‖ + ‖(a - b) * b ^ k‖ := norm_add_le _ _
      _ ≤ C * (k * C ^ k * ‖a - b‖) + ‖a - b‖ * C ^ (k + 1) := by linarith
      _ = ((k + 1 : ℕ) : ℝ) * C ^ (k + 1) * ‖a - b‖ := by
        push_cast; ring

variable [NormedAlgebra ℝ A] [CompleteSpace A]

theorem tendsto_pow_of_hasDerivAt (h1 : ‖(1 : A)‖ ≤ 1) (γ : ℝ → A) (Y : A) (h0 : γ 0 = 1)
    (hd : HasDerivAt γ Y 0) (t : ℝ) :
    Tendsto (fun k : ℕ => γ (t / k) ^ k) atTop (𝓝 (NormedSpace.exp (t • Y))) := by
  set E : ℝ → A := fun s => NormedSpace.exp (s • Y) with hE
  have hE0 : E 0 = 1 := by simp [hE]
  have hEd : HasDerivAt E Y 0 := by
    have := hasDerivAt_exp_smul_const (𝕂 := ℝ) Y (0 : ℝ)
    simpa using this
  have hs : Tendsto (fun k : ℕ => t / (k : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat t
  obtain ⟨M1, hM1⟩ := hd.isBigO_sub.bound
  obtain ⟨M2, hM2⟩ := hEd.isBigO_sub.bound
  set M : ℝ := max (max M1 M2) 0 with hM
  have hM0 : 0 ≤ M := le_max_right _ _
  set c : ℝ := M * |t| with hc
  have hc0 : 0 ≤ c := by positivity
  have hbound : ∀ (f : ℝ → A) (M' : ℝ), M' ≤ M → f 0 = 1 →
      (∀ᶠ s in 𝓝 (0 : ℝ), ‖f s - f 0‖ ≤ M' * ‖s - 0‖) →
      ∀ᶠ k : ℕ in atTop, ‖f (t / k)‖ ≤ 1 + c / k := by
    intro f M' hM' hf hb
    filter_upwards [hs.eventually hb, eventually_gt_atTop 0] with k hk hk0
    have hk' : (0 : ℝ) < k := by exact_mod_cast hk0
    rw [hf] at hk
    have e : f (t / k) = 1 + (f (t / k) - 1) := by abel
    rw [e]
    refine (norm_add_le _ _).trans (add_le_add h1 (hk.trans ?_))
    have : ‖t / (k : ℝ) - 0‖ = |t| / k := by
      simp [abs_div]
    rw [this, hc, mul_div_assoc]
    gcongr
  have ha := hbound γ M1 ((le_max_left _ _).trans (le_max_left _ _)) h0 hM1
  have hb := hbound E M2 ((le_max_right _ _).trans (le_max_left _ _)) hE0 hM2
  have hpow : ∀ k : ℕ, 0 < k → (1 + c / k) ^ k ≤ Real.exp c := by
    intro k hk
    have hk' : (k : ℝ) ≠ 0 := by positivity
    calc (1 + c / k) ^ k ≤ (Real.exp (c / k)) ^ k := by
          gcongr
          rw [add_comm]
          exact Real.add_one_le_exp _
      _ = Real.exp c := by
          rw [← Real.exp_nat_mul]
          congr 1
          field_simp
  have hD : HasDerivAt (fun s => γ s - E s) 0 0 := by
    have := hd.sub hEd
    rw [sub_self] at this
    exact this
  have hlo : (fun s => γ s - E s) =o[𝓝 0] (fun s : ℝ => s) := by
    have := hasDerivAt_iff_isLittleO_nhds_zero.1 hD
    simpa [h0, hE0] using this
  have hK : Tendsto (fun k : ℕ => Real.exp c * ((k : ℝ) * ‖γ (t / k) - E (t / k)‖)) atTop (𝓝 0) := by
    have : Tendsto (fun k : ℕ => (k : ℝ) * ‖γ (t / k) - E (t / k)‖) atTop (𝓝 0) := by
      rw [Metric.tendsto_nhds]
      intro ε hε
      have hp : 0 < |t| + 1 := by positivity
      have hcε : 0 < ε / (|t| + 1) := by positivity
      filter_upwards [(hlo.comp_tendsto hs).def hcε, eventually_gt_atTop 0] with k hk hk0
      have hk' : (0 : ℝ) < k := by exact_mod_cast hk0
      simp only [Function.comp] at hk
      have e : ‖t / (k : ℝ)‖ = |t| / k := by simp [abs_div]
      rw [e] at hk
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)]
      calc (k : ℝ) * ‖γ (t / k) - E (t / k)‖ ≤ k * (ε / (|t| + 1) * (|t| / k)) := by gcongr
        _ = ε * (|t| / (|t| + 1)) := by field_simp
        _ < ε * 1 := by
          gcongr
          rw [div_lt_one hp]
          linarith
        _ = ε := mul_one _
    simpa using this.const_mul (Real.exp c)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hK
  filter_upwards [ha, hb, eventually_gt_atTop 0] with k hak hbk hk0
  have hk' : (k : ℝ) ≠ 0 := by positivity
  have hC : 1 ≤ 1 + c / k := by
    have : 0 ≤ c / k := by positivity
    linarith
  have hEk : NormedSpace.exp (t • Y) = E (t / k) ^ k := by
    simp only [hE]
    letI : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
    rw [← NormedSpace.exp_nsmul]
    congr 1
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    congr 1
    field_simp
  rw [hEk]
  refine (norm_pow_sub_pow_le h1 hC hak hbk k).trans ?_
  have := hpow k hk0
  have hn : 0 ≤ ‖γ (t / k) - E (t / k)‖ := norm_nonneg _
  calc (k : ℝ) * (1 + c / k) ^ k * ‖γ (t / k) - E (t / k)‖
      ≤ k * Real.exp c * ‖γ (t / k) - E (t / k)‖ := by gcongr
    _ = Real.exp c * ((k : ℝ) * ‖γ (t / k) - E (t / k)‖) := by ring

end Abstract

theorem matrix_tendsto (n : ℕ) (γ : ℝ → Matrix (Fin n) (Fin n) ℂ) (Y : Matrix (Fin n) (Fin n) ℂ)
    (h0 : γ 0 = 1) (hd : HasDerivAt γ Y 0) (t : ℝ) :
    Tendsto (fun k : ℕ => γ (t / k) ^ k) atTop (𝓝 (NormedSpace.exp ((t : ℂ) • Y))) := by
  have hs := hasDerivAt_iff_tendsto_slope.1 hd
  letI R : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  letI Al : NormedAlgebra ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  haveI : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℝ _
  have h1 : ‖(1 : Matrix (Fin n) (Fin n) ℂ)‖ ≤ 1 := by
    rw [← Matrix.diagonal_one, Matrix.linfty_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg zero_le_one).2 fun _ => by simp
  have hd' : HasDerivAt γ Y 0 := hasDerivAt_iff_tendsto_slope.2 hs
  have key := @tendsto_pow_of_hasDerivAt _ R Al this h1 γ Y h0 hd' t
  have e : (t : ℂ) • Y = t • Y := by
    ext i j
    simp
  rw [e]
  exact key

theorem tangent_mem_lieAlg : ∀ (n : ℕ) (G : Set (Matrix (Fin n) (Fin n) ℂ)), IsClosedMatrixGroup G →
    ∀ (γ : ℝ → Matrix (Fin n) (Fin n) ℂ) (Y : Matrix (Fin n) (Fin n) ℂ), γ 0 = 1 →
      (∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ G) → HasDerivAt γ Y 0 → Y ∈ lieAlg G := by
  intro n G hG γ Y h0 hev hd t
  obtain ⟨hcl, h1G, hmul, -⟩ := hG
  have hpowG : ∀ g ∈ G, ∀ k : ℕ, g ^ k ∈ G := by
    intro g hg k
    induction k with
    | zero => simpa using h1G
    | succ k ih => rw [pow_succ]; exact hmul _ ih _ hg
  have hs : Tendsto (fun k : ℕ => t / (k : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat t
  refine hcl.mem_of_tendsto (matrix_tendsto n γ Y h0 hd t) ?_
  filter_upwards [hs.eventually hev] with k hk
  exact hpowG _ hk k

end GlobalTheory.CompanionTheory.SmTangent
