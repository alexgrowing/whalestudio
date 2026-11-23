import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.LevelOneQExpansion
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.JQExpansion
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open UpperHalfPlane ModularForm GroundTheory.Global.Elliptic Polynomial Filter Topology
open scoped Real MatrixGroups Manifold

local notation "𝕢" => Function.Periodic.qParam

noncomputable section

namespace LevelOneQExpansion

def term (a : PowerSeries ℤ) (z : ℂ) (n : ℕ) : ℂ := (a.coeff n : ℂ) * z ^ n

theorem exists_norm_term_le {a : PowerSeries ℤ} {z₀ : ℂ} (hz₀ : z₀ ≠ 0)
    (h : Summable (term a z₀)) :
    ∃ M : ℝ, ∀ (z : ℂ) (n : ℕ), ‖term a z n‖ ≤ M * (‖z‖ / ‖z₀‖) ^ n := by
  obtain ⟨M, hM⟩ := h.tendsto_atTop_zero.norm.bddAbove_range
  refine ⟨M, fun z n ↦ ?_⟩
  have h1 : ‖term a z₀ n‖ ≤ M := hM ⟨n, rfl⟩
  have h0 : 0 < ‖z₀‖ := norm_pos_iff.2 hz₀
  have h2 : ‖z₀‖ * (‖z‖ / ‖z₀‖) = ‖z‖ := by field_simp
  have : ‖term a z n‖ = ‖term a z₀ n‖ * (‖z‖ / ‖z₀‖) ^ n := by
    simp only [term, norm_mul, norm_pow]
    rw [mul_assoc, ← mul_pow, h2]
  rw [this]
  exact mul_le_mul_of_nonneg_right h1 (by positivity)

theorem exists_bound {a : PowerSeries ℤ} {B : ℝ} {F : ℍ → ℂ}
    (h : ∀ τ : ℍ, B < τ.im → HasSum (term a (𝕢 1 τ)) (F τ)) :
    ∃ B' r M : ℝ, B ≤ B' ∧ 0 < r ∧ (∀ τ : ℍ, B' < τ.im → ‖𝕢 1 (τ : ℂ)‖ < r) ∧
      ∀ (z : ℂ) (n : ℕ), ‖term a z n‖ ≤ M * (‖z‖ / r) ^ n := by
  have hB0 := le_max_left B 0
  have hb0 := le_max_right B 0
  set b : ℝ := max B 0 + 1 with hbdef
  have hb : 0 < b := by linarith
  let τ₀ : ℍ := ⟨(b : ℂ) * Complex.I, by simpa using hb⟩
  have hτ₀ : τ₀.im = b := by simp [τ₀, UpperHalfPlane.im]
  have hq₀ : 𝕢 1 (τ₀ : ℂ) ≠ 0 := Function.Periodic.qParam_ne_zero _
  obtain ⟨M, hM⟩ := exists_norm_term_le hq₀ (h τ₀ (by rw [hτ₀]; linarith)).summable
  refine ⟨b, ‖𝕢 1 (τ₀ : ℂ)‖, M, by linarith, norm_pos_iff.2 hq₀, fun τ hτ ↦ ?_, hM⟩
  rw [Function.Periodic.norm_qParam, Function.Periodic.norm_qParam, Real.exp_lt_exp]
  simp only [UpperHalfPlane.coe_im, div_one, hτ₀]
  nlinarith [Real.pi_pos]

theorem summable_norm_term {a : PowerSeries ℤ} {r M : ℝ} (hr : 0 < r)
    (hM : ∀ (z : ℂ) (n : ℕ), ‖term a z n‖ ≤ M * (‖z‖ / r) ^ n) {z : ℂ} (hz : ‖z‖ < r) :
    Summable fun n ↦ ‖term a z n‖ := by
  have hρ : ‖z‖ / r < 1 := (div_lt_one hr).2 hz
  exact Summable.of_nonneg_of_le (fun n ↦ norm_nonneg _) (hM z)
    ((summable_geometric_of_lt_one (by positivity) hρ).mul_left M)

theorem hasSum_term_mul {a b : PowerSeries ℤ} {z u v : ℂ}
    (ha : Summable fun n ↦ ‖term a z n‖) (hb : Summable fun n ↦ ‖term b z n‖)
    (hu : HasSum (term a z) u) (hv : HasSum (term b z) v) :
    HasSum (term (a * b) z) (u * v) ∧ Summable fun n ↦ ‖term (a * b) z n‖ := by
  have key : term (a * b) z =
      fun n ↦ ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n, term a z kl.1 * term b z kl.2 := by
    funext n
    simp only [term, PowerSeries.coeff_mul, Int.cast_sum, Int.cast_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun kl hkl ↦ ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hkl
    rw [← hkl, pow_add]
    ring
  rw [key]
  have hs := summable_norm_sum_mul_antidiagonal_of_summable_norm ha hb
  refine ⟨?_, hs⟩
  have ht := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm ha hb
  rw [hu.tsum_eq, hv.tsum_eq] at ht
  rw [ht]
  exact hs.of_norm.hasSum

theorem hasSum_term_pow {a : PowerSeries ℤ} {z u : ℂ}
    (ha : Summable fun n ↦ ‖term a z n‖) (hu : HasSum (term a z) u) (N : ℕ) :
    HasSum (term (a ^ N) z) (u ^ N) ∧ Summable fun n ↦ ‖term (a ^ N) z n‖ := by
  induction N with
  | zero =>
    have h1 : term (1 : PowerSeries ℤ) z = fun n ↦ if n = 0 then 1 else 0 := by
      funext n
      by_cases hn : n = 0 <;> simp [term, PowerSeries.coeff_one, hn]
    simp only [pow_zero, h1]
    refine ⟨hasSum_ite_eq 0 1, summable_of_ne_finset_zero (s := {0}) fun n hn ↦ ?_⟩
    simp only [Finset.mem_singleton] at hn
    simp [hn]
  | succ N ih =>
    rw [pow_succ, pow_succ]
    exact hasSum_term_mul ih.2 ha ih.1 hu

theorem tendsto_of_hasSum {a : PowerSeries ℤ} {B : ℝ} {F : ℍ → ℂ}
    (h : ∀ τ : ℍ, B < τ.im → HasSum (term a (𝕢 1 τ)) (F τ)) :
    Tendsto F atImInfty (𝓝 (a.coeff 0 : ℂ)) := by
  obtain ⟨B', r, M, hBB, hr, hq, hM⟩ := exists_bound h
  have hM0 : 0 ≤ M := by simpa using (norm_nonneg _).trans (hM 0 0)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hq0 : Tendsto (fun τ : ℍ ↦ 𝕢 1 (τ : ℂ)) atImInfty (𝓝 0) :=
    UpperHalfPlane.qParam_tendsto_atImInfty one_pos
  have hlim : Tendsto (fun τ : ℍ ↦ 2 * M / r * ‖𝕢 1 (τ : ℂ)‖) atImInfty (𝓝 0) := by
    simpa using hq0.norm.const_mul (2 * M / r)
  refine squeeze_zero' (Eventually.of_forall fun τ ↦ norm_nonneg _) ?_ hlim
  have hev1 : ∀ᶠ τ : ℍ in atImInfty, B' < τ.im :=
    (atImInfty_mem _).2 ⟨B' + 1, fun τ hτ ↦ by show B' < τ.im; linarith⟩
  have hev2 : ∀ᶠ τ : ℍ in atImInfty, ‖𝕢 1 (τ : ℂ)‖ < r / 2 := by
    have := hq0.norm
    rw [norm_zero] at this
    exact this.eventually (gt_mem_nhds (by linarith))
  filter_upwards [hev1, hev2] with τ h1 h2
  set q := 𝕢 1 (τ : ℂ)
  set ρ := ‖q‖ / r with hρdef
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : ρ ≤ 1 / 2 := by rw [hρdef, div_le_iff₀ hr]; linarith
  have hs := (hasSum_nat_add_iff' 1).2 (h τ (by linarith))
  simp only [Finset.range_one, Finset.sum_singleton, term, pow_zero, mul_one] at hs
  have hg : HasSum (fun n : ℕ ↦ M * ρ * ρ ^ n) (M * ρ * (1 - ρ)⁻¹) :=
    (hasSum_geometric_of_lt_one hρ0 (by linarith)).mul_left (M * ρ)
  have hle := hs.norm_le_of_bounded hg fun n ↦ by
    have := hM q (n + 1)
    simp only [term] at this
    calc _ ≤ M * ρ ^ (n + 1) := this
      _ = M * ρ * ρ ^ n := by ring
  have hinv : (1 - ρ)⁻¹ ≤ 2 := by
    have h1 : 0 < 1 - ρ := by linarith
    rw [inv_eq_one_div, div_le_iff₀ h1]
    linarith
  calc ‖F τ - (a.coeff 0 : ℂ)‖ ≤ M * ρ * (1 - ρ)⁻¹ := hle
    _ ≤ M * ρ * 2 := mul_le_mul_of_nonneg_left hinv (mul_nonneg hM0 hρ0)
    _ = 2 * M / r * ‖q‖ := by rw [hρdef]; ring

theorem eq_const_of_hasSum {f : ℍ → ℂ} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hinv : ∀ (γ : SL(2, ℤ)) (τ : ℍ), f (γ • τ) = f τ) {a : PowerSeries ℤ} {B : ℝ}
    (h : ∀ τ : ℍ, B < τ.im → HasSum (term a (𝕢 1 τ)) (f τ)) (τ : ℍ) :
    f τ = a.coeff 0 := by
  have hlim := tendsto_of_hasSum h
  have hslash : ∀ γ : SL(2, ℤ), f ∣[(0 : ℤ)] γ = f := fun γ ↦ by
    funext τ
    simp only [SL_slash_apply, neg_zero, zpow_zero, mul_one]
    exact hinv γ τ
  let F : ModularForm 𝒮ℒ 0 :=
    { toFun := f
      slash_action_eq' := fun _ ⟨γ, hγ⟩ ↦ hγ ▸ hslash γ
      holo' := hf
      bdd_at_cusps' := fun {c} hc ↦ by
        rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
        rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
        intro γ _
        rw [hslash γ, IsBoundedAtImInfty, BoundedAtFilter]
        exact hlim.isBigO_one ℝ }
  obtain ⟨c, hc⟩ := ModularFormClass.levelOne_weight_zero_const F
  have hfc : f = Function.const ℍ c := hc
  have hc' : Tendsto f atImInfty (𝓝 c) := by
    rw [hfc]
    exact tendsto_const_nhds
  rw [hfc, Function.const_apply, tendsto_nhds_unique hc' hlim]

theorem exists_poly (hJ : JQExpansion.Statement) (N : ℕ) :
    ∀ f : ℍ → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f → (∀ (γ : SL(2, ℤ)) (τ : ℍ), f (γ • τ) = f τ) →
    ∀ (a : PowerSeries ℤ) (B : ℝ),
      (∀ τ : ℍ, B < τ.im → HasSum (term a (𝕢 1 τ)) (𝕢 1 (τ : ℂ) ^ N * f τ)) →
      ∃ Q : ℤ[X], ∀ τ : ℍ, f τ = aeval (modularJ τ) Q := by
  obtain ⟨c, hc0, hc⟩ := hJ
  set J : PowerSeries ℤ := PowerSeries.mk c with hJdef
  have hJt : ∀ τ : ℍ, HasSum (term J (𝕢 1 τ)) (𝕢 1 (τ : ℂ) * modularJ τ) := fun τ ↦ by
    convert hc τ using 1
    funext n
    simp [term, J]
  have hJ0 : J.coeff 0 = 1 := by simp [J, hc0]
  have hjd : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) modularJ :=
    UpperHalfPlane.mdifferentiable_iff.2 differentiableOn_modularJC
  obtain ⟨B₂, r₂, M₂, -, hr₂, hq₂, hM₂⟩ := exists_bound (B := 0) fun τ _ ↦ hJt τ
  induction N with
  | zero =>
    intro f hf hinv a B h
    refine ⟨C (a.coeff 0), fun τ ↦ ?_⟩
    rw [eq_const_of_hasSum hf hinv (B := B) (fun τ hτ ↦ by simpa using h τ hτ) τ]
    simp
  | succ N ih =>
    intro f hf hinv a B h
    set c₀ := a.coeff 0 with hc₀
    let g : ℍ → ℂ := fun τ ↦ f τ - c₀ * modularJ τ ^ (N + 1)
    have hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g := hf.sub (mdifferentiable_const.mul (hjd.pow _))
    have hginv : ∀ (γ : SL(2, ℤ)) (τ : ℍ), g (γ • τ) = g τ := fun γ τ ↦ by
      simp only [g]
      rw [hinv, modularJ_smul]
    obtain ⟨B₁, r₁, M₁, hB₁, hr₁, hq₁, hM₁⟩ := exists_bound h
    set R : PowerSeries ℤ := a - c₀ • J ^ (N + 1) with hRdef
    have hJp : (J ^ (N + 1)).coeff 0 = 1 := by
      rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow,
        ← PowerSeries.coeff_zero_eq_constantCoeff_apply, hJ0, one_pow]
    have hR0 : R.coeff 0 = 0 := by
      rw [hRdef, map_sub, map_smul, hJp, smul_eq_mul, mul_one, hc₀, sub_self]
    have hser : ∀ τ : ℍ, max B₁ B₂ < τ.im → HasSum (term (PowerSeries.mk fun n ↦ R.coeff (n + 1))
        (𝕢 1 τ)) (𝕢 1 (τ : ℂ) ^ N * g τ) := by
      intro τ hτ
      set q := 𝕢 1 (τ : ℂ)
      have hq : q ≠ 0 := Function.Periodic.qParam_ne_zero _
      have hτ₁ : B₁ < τ.im := lt_of_le_of_lt (le_max_left _ _) hτ
      have hτ₂ : B₂ < τ.im := lt_of_le_of_lt (le_max_right _ _) hτ
      have hJs := summable_norm_term hr₂ hM₂ (hq₂ τ hτ₂)
      have hpow := (hasSum_term_pow hJs (hJt τ) (N + 1)).1
      have ha := h τ (lt_of_le_of_lt hB₁ hτ₁)
      have hRs : HasSum (term R q) (q ^ (N + 1) * f τ - c₀ * (q * modularJ τ) ^ (N + 1)) := by
        have : term R q = fun n ↦ term a q n - c₀ * term (J ^ (N + 1)) q n := by
          funext n
          simp only [term, hRdef]
          rw [map_sub, map_smul, smul_eq_mul]
          push_cast
          ring
        rw [this]
        exact ha.sub (hpow.mul_left _)
      have h1 := (hasSum_nat_add_iff' 1).2 hRs
      simp only [Finset.range_one, Finset.sum_singleton, term, hR0, Int.cast_zero, zero_mul,
        sub_zero] at h1
      have h2 := h1.mul_left q⁻¹
      have e1 : (fun i ↦ q⁻¹ * (↑(R.coeff (i + 1)) * q ^ (i + 1))) =
          term (PowerSeries.mk fun n ↦ R.coeff (n + 1)) q := by
        funext n
        simp only [term, PowerSeries.coeff_mk, pow_succ]
        field_simp
      have e2 : q⁻¹ * (q ^ (N + 1) * f τ - ↑c₀ * (q * modularJ τ) ^ (N + 1)) = q ^ N * g τ := by
        simp only [g]
        field_simp
        ring
      rw [e1, e2] at h2
      exact h2
    obtain ⟨Q, hQ⟩ := ih g hg hginv _ _ hser
    refine ⟨Q + Polynomial.C c₀ * X ^ (N + 1), fun τ ↦ ?_⟩
    have := hQ τ
    simp only [g] at this
    simp [← this]

end LevelOneQExpansion

open LevelOneQExpansion in

theorem LevelOneQExpansion.proof (hJ : JQExpansion.Statement) : LevelOneQExpansion.Statement := by
  rintro f hf hinv ⟨N, c, A, h⟩
  exact exists_poly hJ N f hf hinv (PowerSeries.mk c) A fun τ hτ ↦ by
    convert h τ hτ using 1
    funext n
    simp [term]

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
