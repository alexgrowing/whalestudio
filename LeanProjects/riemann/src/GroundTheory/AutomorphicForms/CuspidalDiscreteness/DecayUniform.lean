import Mathlib
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.ExistsNormRconvLeSiegel

open MeasureTheory Set Filter Topology Function
open NumberField IsDedekindDomain
open scoped ENNReal Pointwise NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

set_option linter.unusedSectionVars false

namespace CuspidalSpectrum

open Reduction AutomorphicForm RightCosetSpace

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

local notation "Γ₁" => rationalGLOne K n

variable (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]

theorem exists_norm_rconv_le_siegel_basic (f : CompactlySupportedContinuousMap (normOneGL K n) ℂ)
    {ω : Set (AdelicGLn.AdelicGL K n)} (hω : IsCompact ω) {t : ℝ} (ht : 0 < t) :
    ∃ (C : ℝ) (N : ℕ), ∀ φ : Lp ℂ 2 (quotientMeasure Γ₁ μ), ∀ b ∈ ω, ∀ (ρ : Fin n → ℝ)
      (hρ : ∀ i, 0 < ρ i), (∀ i j : Fin n, (j : ℕ) = i + 1 → t * ρ j ≤ ρ i) →
      ∀ kk ∈ (maxCompact : Subgroup (AdelicGLn.AdelicGL K n)), ∀ x : normOneGL K n,
      (x : AdelicGLn.AdelicGL K n) = b * diagUnits n (fun i => posIdele (K := K) (ρ i) (hρ i)) * kk →
      ∀ R : ℝ, 1 ≤ R → (∀ i j : Fin n, i < j → ρ i / ρ j ≤ R) →
      ‖rconv Γ₁ μ f φ x‖ ≤ C * √(R ^ N) * ‖φ‖ := by
  obtain ⟨Cc, N, hCc⟩ := exists_encard_le_siegel hω ht f.hasCompactSupport
  have hf2 : ∫⁻ y, ‖f y‖ₑ ^ 2 ∂μ ≠ ⊤ := by
    have := (f.continuous.memLp_of_hasCompactSupport (μ := μ) (p := 2) f.hasCompactSupport).2
    rw [← L2Kernel.eLpNorm_two_sq]
    exact (ENNReal.pow_lt_top this).ne
  set A := (∫⁻ y, ‖f y‖ₑ ^ 2 ∂μ).toReal
  have hA : 0 ≤ A := ENNReal.toReal_nonneg
  refine ⟨√(A * max Cc 0), N, ?_⟩
  intro φ b hb ρ hρ hsieg kk hkk x hx R hR1 hR
  obtain ⟨m, hmC, hm⟩ := hCc b hb ρ hρ hsieg kk hkk x hx R hR1 hR
  have hS : MeasurableSet ((fun y => x * y) '' tsupport (f : normOneGL K n → ℂ)) :=
    (f.hasCompactSupport.image (continuous_const_mul x)).measurableSet
  have h1 := enorm_rconv_sq_le Γ₁ μ f φ x hS (fun y hy => image_eq_zero_of_notMem_tsupport
    fun h' => hy ⟨x⁻¹ * y, h', by simp⟩) hm
  rw [← mul_assoc] at h1
  have h2 := norm_le_of_enorm_sq_le (ENNReal.mul_ne_top hf2 (by simp)) h1
  refine h2.trans ?_
  gcongr
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ← Real.sqrt_mul (mul_nonneg hA
    (le_max_right _ _))]
  refine Real.sqrt_le_sqrt ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left (hmC.trans ?_) hA
  exact mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (by linarith) _)

theorem exists_le_max_pow (hn : 2 ≤ n) (ρ : Fin n → ℝ) (hρ : ∀ i, 0 < ρ i) :
    ∃ (r : ℕ) (hr : 0 < r) (hrn : r < n), ∀ i j : Fin n, i < j →
      ρ i / ρ j ≤ max 1 (ρ ⟨r - 1, by omega⟩ / ρ ⟨r, hrn⟩) ^ n := by
  have : Nonempty (Fin (n - 1)) := ⟨⟨0, by omega⟩⟩
  obtain ⟨l₀, hl₀⟩ := Finite.exists_max fun l : Fin (n - 1) =>
    ρ ⟨l, by omega⟩ / ρ ⟨l + 1, by omega⟩
  refine ⟨l₀ + 1, by omega, by omega, fun i j hij => ?_⟩
  set M := max 1 (ρ ⟨l₀ + 1 - 1, by omega⟩ / ρ ⟨l₀ + 1, by omega⟩)
  have hM1 : 1 ≤ M := le_max_left _ _
  have hstep : ∀ l : ℕ, ∀ (hl : l + 1 < n), ρ ⟨l, by omega⟩ ≤ M * ρ ⟨l + 1, hl⟩ := by
    intro l hl
    have h1 := hl₀ ⟨l, by omega⟩
    rw [← div_le_iff₀ (hρ _)]
    exact h1.trans (le_max_right _ _)
  have hchain : ∀ d : ℕ, ∀ (a : ℕ) (ha : a + d < n), ρ ⟨a, by omega⟩ ≤ M ^ d * ρ ⟨a + d, ha⟩ := by
    intro d
    induction d with
    | zero => intro a ha; simp
    | succ d ih =>
      intro a ha
      calc ρ ⟨a, by omega⟩ ≤ M ^ d * ρ ⟨a + d, by omega⟩ := ih a (by omega)
        _ ≤ M ^ d * (M * ρ ⟨a + d + 1, by omega⟩) :=
            mul_le_mul_of_nonneg_left (hstep (a + d) (by omega)) (pow_nonneg (by linarith) _)
        _ = M ^ (d + 1) * ρ ⟨a + (d + 1), ha⟩ := by rw [pow_succ]; ring_nf
  have hij' : (i : ℕ) < j := hij
  have h1 := hchain (j - i) i (by omega)
  have hj : (⟨(i : ℕ) + (j - i), by omega⟩ : Fin n) = j := Fin.ext (by simp; omega)
  rw [hj] at h1
  rw [div_le_iff₀ (hρ _)]
  calc ρ i = ρ ⟨i, by omega⟩ := rfl
    _ ≤ M ^ ((j : ℕ) - i) * ρ j := h1
    _ ≤ M ^ n * ρ j := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hM1 (by omega)) (hρ _).le

variable (ν : Measure (ArchUnits K n)) [ν.IsHaarMeasure]

theorem exists_norm_rconv_le_decay {β : ArchMatrix K n → ℝ}
    (hβ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) β) (hβc : HasCompactSupport β)
    (hβu : tsupport β ⊆ range (Units.val : ArchUnits K n → ArchMatrix K n))
    (U : Subgroup (AdelicGLn.integralFiniteGL K n))
    (hU : IsOpen (U : Set (AdelicGLn.integralFiniteGL K n)))
    (g : CompactlySupportedContinuousMap (normOneGL K n) ℂ)
    {ω : Set (AdelicGLn.AdelicGL K n)} (hω : IsCompact ω)
    (hωB : ω ⊆ ((adelicBorel : Subgroup (AdelicGLn.AdelicGL K n)) : Set (AdelicGLn.AdelicGL K n)))
    {t : ℝ} (ht : 0 < t) (N' : ℕ) :
    ∃ C : ℝ, ∀ φ ∈ cuspidalL2 μ, ∀ b ∈ ω, ∀ (ρ : Fin n → ℝ) (hρ : ∀ i, 0 < ρ i),
      (∀ i j : Fin n, (j : ℕ) = i + 1 → t * ρ j ≤ ρ i) →
      ∀ kk ∈ (maxCompact : Subgroup (AdelicGLn.AdelicGL K n)), ∀ x : normOneGL K n,
      (x : AdelicGLn.AdelicGL K n) = b * diagUnits n (fun i => posIdele (K := K) (ρ i) (hρ i)) * kk →
      ∀ R : ℝ, 1 ≤ R → (∃ i j : Fin n, i < j ∧ R ≤ ρ i / ρ j) →
      ‖rconv Γ₁ μ (archConv ν hβ.continuous hβc hβu (finAvg U hU g)) φ x‖ ≤
        C * (R ^ N')⁻¹ * ‖φ‖ := by
  set f := archConv ν hβ.continuous hβc hβu (finAvg U hU g)
  obtain ⟨C₀, N₀, hC₀⟩ := exists_norm_rconv_le_siegel_basic μ f hω ht
  have hdec := fun (r : ℕ) (hr : 0 < r) (hrn : r < n) =>
    exists_norm_rconv_le_siegel μ ν hβ hβc hβu U hU g hω hωB ht hr hrn
  choose Nf hNf using hdec
  have hdec2 := fun (r : ℕ) (hr : 0 < r) (hrn : r < n) =>
    hNf r hr hrn (n * Nf r hr hrn + n * N')
  choose Cf hCf using hdec2
  set Cmax := max C₀ 0 + ∑ r : Fin n, if h : 0 < (r : ℕ) then max (Cf r h r.2) 0 else 0
  have hsum0 : 0 ≤ ∑ r : Fin n, if h : 0 < (r : ℕ) then max (Cf r h r.2) 0 else 0 :=
    Finset.sum_nonneg fun r _ => by split_ifs <;> simp
  have hCf_le : ∀ (r : ℕ) (hr : 0 < r) (hrn : r < n), Cf r hr hrn ≤ Cmax := by
    intro r hr hrn
    have h1 := Finset.single_le_sum (f := fun r : Fin n =>
      if h : 0 < (r : ℕ) then max (Cf r h r.2) 0 else 0)
      (fun r _ => by split_ifs <;> simp) (Finset.mem_univ ⟨r, hrn⟩)
    simp only [hr, dif_pos] at h1
    exact (le_max_left _ _).trans (h1.trans (le_add_of_nonneg_left (le_max_right _ _)))
  have hC₀_le : C₀ ≤ Cmax := (le_max_left _ _).trans (le_add_of_nonneg_right hsum0)
  have hCmax0 : 0 ≤ Cmax := (le_max_right _ _).trans (le_add_of_nonneg_right hsum0)
  refine ⟨Cmax, ?_⟩
  intro φ hφ b hb ρ hρ hsieg kk hkk x hx R hR1 ⟨i₀, j₀, hij₀, hRij⟩
  have hn : 2 ≤ n := by
    have : (i₀ : ℕ) < j₀ := hij₀
    omega
  obtain ⟨r, hr, hrn, hratio⟩ := exists_le_max_pow hn ρ hρ
  set α := ρ ⟨r - 1, by omega⟩ / ρ ⟨r, hrn⟩
  have hα0 : 0 < α := div_pos (hρ _) (hρ _)
  rcases le_or_gt α 1 with hα1 | hα1
  · have hM : max 1 α = 1 := max_eq_left hα1
    have hR1' : R = 1 := le_antisymm (hRij.trans ((hratio i₀ j₀ hij₀).trans
      (by rw [hM, one_pow]))) hR1
    have h := hC₀ φ b hb ρ hρ hsieg kk hkk x hx 1 le_rfl fun i j hij =>
      (hratio i j hij).trans (by rw [hM, one_pow])
    rw [one_pow, Real.sqrt_one, mul_one] at h
    rw [hR1', one_pow, inv_one, mul_one]
    exact h.trans (mul_le_mul_of_nonneg_right hC₀_le (norm_nonneg _))
  · have hM : max 1 α = α := max_eq_right hα1.le
    have h := hCf r hr hrn φ hφ b hb ρ hρ hsieg kk hkk x hx (α ^ n) (one_le_pow₀ hα1.le)
      fun i j hij => (hratio i j hij).trans (by rw [hM])
    have hgain : ρ ⟨r, hrn⟩ / ρ ⟨r - 1, by omega⟩ = α⁻¹ := by rw [inv_div]
    rw [hgain] at h
    set a := n * Nf r hr hrn
    set c := n * N'
    have hy1 : 1 ≤ α ^ a := one_le_pow₀ hα1.le
    have hsq : √((α ^ n) ^ Nf r hr hrn) ≤ α ^ a := by
      rw [← pow_mul]
      calc √(α ^ a) ≤ √((α ^ a) ^ 2) := Real.sqrt_le_sqrt (le_self_pow₀ hy1 two_ne_zero)
        _ = α ^ a := Real.sqrt_sq (by positivity)
    have hpow : (α⁻¹) ^ (a + c) * α ^ a = (α ^ c)⁻¹ := by
      rw [inv_pow, pow_add]
      field_simp
    have hRc : (α ^ c)⁻¹ ≤ (R ^ N')⁻¹ := by
      have hRα : R ≤ α ^ n := hRij.trans ((hratio i₀ j₀ hij₀).trans (by rw [hM]))
      rw [show c = n * N' from rfl, pow_mul]
      exact inv_anti₀ (pow_pos (by linarith) _) (pow_le_pow_left₀ (by linarith) hRα _)
    have hX : 0 ≤ (α⁻¹) ^ (a + c) * √((α ^ n) ^ Nf r hr hrn) := by positivity
    calc ‖rconv Γ₁ μ f φ x‖
        ≤ Cf r hr hrn * (α⁻¹) ^ (a + c) * √((α ^ n) ^ Nf r hr hrn) * ‖φ‖ := h
      _ ≤ Cmax * ((α⁻¹) ^ (a + c) * α ^ a) * ‖φ‖ := by
          rw [mul_assoc (Cf r hr hrn)]
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
          calc Cf r hr hrn * ((α⁻¹) ^ (a + c) * √((α ^ n) ^ Nf r hr hrn))
              ≤ Cmax * ((α⁻¹) ^ (a + c) * √((α ^ n) ^ Nf r hr hrn)) :=
                mul_le_mul_of_nonneg_right (hCf_le r hr hrn) hX
            _ ≤ Cmax * ((α⁻¹) ^ (a + c) * α ^ a) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsq (by positivity)) hCmax0
      _ = Cmax * (α ^ c)⁻¹ * ‖φ‖ := by rw [hpow]
      _ ≤ Cmax * (R ^ N')⁻¹ * ‖φ‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hRc hCmax0) (norm_nonneg _)

theorem exists_norm_rconv_le_uniform {β : ArchMatrix K n → ℝ}
    (hβ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) β) (hβc : HasCompactSupport β)
    (hβu : tsupport β ⊆ range (Units.val : ArchUnits K n → ArchMatrix K n))
    (U : Subgroup (AdelicGLn.integralFiniteGL K n))
    (hU : IsOpen (U : Set (AdelicGLn.integralFiniteGL K n)))
    (g : CompactlySupportedContinuousMap (normOneGL K n) ℂ) :
    ∃ B : ℝ, ∀ φ ∈ cuspidalL2 μ, ∀ x : normOneGL K n,
      ‖rconv Γ₁ μ (archConv ν hβ.continuous hβc hβu (finAvg U hU g)) φ x‖ ≤ B * ‖φ‖ := by
  set f := archConv ν hβ.continuous hβc hβu (finAvg U hU g)
  obtain ⟨ω, hω, hωB, t, ht, hsieg⟩ := exists_siegelSet (K := K) n
  obtain ⟨C₀, N₀, hC₀⟩ := exists_norm_rconv_le_siegel_basic μ f hω ht
  obtain ⟨C₁, hC₁⟩ := exists_norm_rconv_le_decay μ ν hβ hβc hβu U hU g hω hωB ht 0
  refine ⟨max C₀ 0 + max C₁ 0, fun φ hφ x => ?_⟩
  obtain ⟨γ, hγ⟩ := hsieg (x : AdelicGLn.AdelicGL K n)
  have hγ1 : AdelicGLn.diagonal K n γ ∈ normOneGL K n := rationalGL_le_normOneGL ⟨γ, rfl⟩
  set γ₁ : normOneGL K n := ⟨AdelicGLn.diagonal K n γ, hγ1⟩
  have hγΓ : γ₁ ∈ Γ₁ := ⟨γ, rfl⟩
  rw [← rconv_mul_left Γ₁ μ f φ hγΓ x]
  obtain ⟨b, hb, a, ⟨ρ, hρ, hs, rfl⟩, kk, hkk, hx⟩ := hγ
  have hx' : ((γ₁ * x : normOneGL K n) : AdelicGLn.AdelicGL K n) =
      b * diagUnits n (fun i => posIdele (K := K) (ρ i) (hρ i)) * kk := hx
  have hB0 : 0 ≤ max C₀ 0 + max C₁ 0 := add_nonneg (le_max_right _ _) (le_max_right _ _)
  by_cases hcase : ∃ i j : Fin n, i < j ∧ 1 ≤ ρ i / ρ j
  · have h := hC₁ φ hφ b hb ρ hρ hs kk hkk (γ₁ * x) hx' 1 le_rfl hcase
    rw [pow_zero, inv_one, mul_one] at h
    refine h.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    exact (le_max_left _ _).trans (le_add_of_nonneg_left (le_max_right _ _))
  · simp only [not_exists, not_and, not_le] at hcase
    have h := hC₀ φ b hb ρ hρ hs kk hkk (γ₁ * x) hx' 1 le_rfl fun i j hij => (hcase i j hij).le
    rw [one_pow, Real.sqrt_one, mul_one] at h
    refine h.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    exact (le_max_left _ _).trans (le_add_of_nonneg_right (le_max_right _ _))

end CuspidalSpectrum

end

end GroundTheory.Automorphic
