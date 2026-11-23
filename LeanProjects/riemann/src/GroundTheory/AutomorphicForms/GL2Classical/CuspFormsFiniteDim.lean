import Mathlib
import GroundTheory.AutomorphicForms.GL2Classical.EigenQExpansion

open NumberField Matrix CongruenceSubgroup ModularForm Complex Filter
open UpperHalfPlane hiding I I_re I_im
open scoped MatrixGroups ModularForm Real

namespace GroundTheory.Automorphic

noncomputable section

namespace GL2Classical

open AdelicGLn AutomorphicForm

local notation "𝕢₁" => Function.Periodic.qParam 1

variable {N : ℕ} [NeZero N] {k : ℤ}

theorem norm_qParam_one (τ : ℍ) : ‖𝕢₁ (τ : ℂ)‖ = Real.exp (-2 * π * τ.im) := by
  rw [Function.Periodic.norm_qParam]
  simp

theorem exists_norm_le_exp_of_coeff_eq_zero (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k) (B : ℕ)
    (hB : ∀ n ≤ B, (qExpansion 1 f).coeff n = 0) :
    ∃ C, ∀ τ : ℍ, 1 ≤ τ.im → ‖f τ‖ ≤ C * Real.exp (-2 * π * (B + 1) * τ.im) := by
  set a : ℕ → ℂ := fun m => (qExpansion 1 f).coeff m
  set τ₀ : ℍ := ⟨I / 2, by simp⟩
  have h0 := hasSum_qExpansion_cusp f τ₀
  obtain ⟨M0, hM0⟩ := (h0.summable.tendsto_atTop_zero.norm).bddAbove_range
  have hq0 : ‖𝕢₁ (τ₀ : ℂ)‖ = Real.exp (-π) := by
    rw [norm_qParam_one]
    congr 1
    simp [τ₀, UpperHalfPlane.im]
    ring
  have ha : ∀ m : ℕ, ‖a m‖ ≤ M0 * Real.exp (π * m) := by
    intro m
    have hm := hM0 ⟨m, rfl⟩
    simp only at hm
    rw [norm_mul, norm_pow, hq0, ← Real.exp_nat_mul] at hm
    have e : ‖a m‖ = ‖a m‖ * Real.exp (m * -π) * Real.exp (π * m) := by
      rw [mul_assoc, ← Real.exp_add]
      ring_nf
      simp
    rw [e]
    exact mul_le_mul_of_nonneg_right hm (Real.exp_pos _).le
  refine ⟨M0 * Real.exp (π * (B + 1)) * (1 - Real.exp (-π))⁻¹, fun τ hτ => ?_⟩
  have hs := hasSum_qExpansion_cusp f τ
  rw [← hasSum_nat_add_iff' (B + 1)] at hs
  have hzero : ∑ i ∈ Finset.range (B + 1), a i * 𝕢₁ (τ : ℂ) ^ i = 0 :=
    Finset.sum_eq_zero fun i hi => by
      rw [Finset.mem_range] at hi
      simp only [a]
      rw [hB i (by omega), zero_mul]
  rw [hzero, sub_zero] at hs
  set r := ‖𝕢₁ (τ : ℂ)‖ with hrdef
  have hr : r = Real.exp (-2 * π * τ.im) := norm_qParam_one τ
  have hr0 : 0 ≤ r := norm_nonneg _
  have hr1 : r ≤ Real.exp (-2 * π) := by
    rw [hr]
    exact Real.exp_le_exp.2 (by nlinarith [Real.pi_pos])
  have hg : HasSum (fun m : ℕ => M0 * Real.exp (π * (B + 1)) * r ^ (B + 1) * Real.exp (-π) ^ m)
      (M0 * Real.exp (π * (B + 1)) * r ^ (B + 1) * (1 - Real.exp (-π))⁻¹) :=
    (hasSum_geometric_of_lt_one (Real.exp_pos _).le
      (Real.exp_lt_one_iff.2 (by linarith [Real.pi_pos]))).mul_left _
  have hle := hs.norm_le_of_bounded hg (fun m => by
    rw [norm_mul, norm_pow, ← hrdef, pow_add]
    have h1 : r ^ m ≤ Real.exp (-2 * π) ^ m := pow_le_pow_left₀ hr0 hr1 m
    have h2 := ha (m + (B + 1))
    have e1 : Real.exp (-2 * π) ^ m * Real.exp (π * ((m + (B + 1) : ℕ) : ℝ)) =
        Real.exp (π * (B + 1)) * Real.exp (-π) ^ m := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
      congr 1
      push_cast
      ring
    have hM0' : 0 ≤ M0 := le_trans (norm_nonneg _) (hM0 ⟨0, rfl⟩)
    calc ‖a (m + (B + 1))‖ * (r ^ m * r ^ (B + 1))
        ≤ (M0 * Real.exp (π * ((m + (B + 1) : ℕ) : ℝ))) * (Real.exp (-2 * π) ^ m * r ^ (B + 1)) := by
          gcongr
      _ = M0 * Real.exp (π * (B + 1)) * r ^ (B + 1) * Real.exp (-π) ^ m := by
          linear_combination (M0 * r ^ (B + 1)) * e1)
  calc ‖f τ‖ ≤ M0 * Real.exp (π * (B + 1)) * r ^ (B + 1) * (1 - Real.exp (-π))⁻¹ := hle
    _ = M0 * Real.exp (π * (B + 1)) * (1 - Real.exp (-π))⁻¹ * Real.exp (-2 * π * (B + 1) * τ.im) := by
      rw [hr, ← Real.exp_nat_mul]
      push_cast
      ring_nf

variable (N k) in

def sturmBoundGamma0 : ℕ :=
  (k * Nat.card (𝒮ℒ ⧸ (Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ)).toNat / 12

theorem isBoundedAtImInfty_quotientFunc (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k)
    (q : 𝒮ℒ ⧸ (Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) :
    IsBoundedAtImInfty (SlashInvariantForm.quotientFunc f q) := by
  induction q using Quotient.inductionOn with
  | h h =>
    obtain ⟨σ, hσ⟩ := h.2
    rw [SlashInvariantForm.quotientFunc_mk]
    have e : ((h : GL (Fin 2) ℝ))⁻¹ = toReal (Matrix.SpecialLinearGroup.mapGL ℚ σ⁻¹) := by
      rw [toReal_mapGL, map_inv, hσ]
    rw [e]
    exact isBoundedAtImInfty_slash_toReal (CuspForm.toModularFormₗ f) _

theorem eq_zero_of_coeff_le_sturmBound (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k)
    (hB : ∀ n ≤ sturmBoundGamma0 N k, (qExpansion 1 f).coeff n = 0) : f = 0 := by
  classical
  set B := sturmBoundGamma0 N k
  obtain ⟨C, hC⟩ := exists_norm_le_exp_of_coeff_eq_zero f B hB
  set Q := 𝒮ℒ ⧸ (Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ
  set F := ModularForm.norm 𝒮ℒ f
  let : Fintype Q := Fintype.ofFinite Q
  set q₀ : Q := ⟦1⟧

  have hR : IsBoundedAtImInfty (∏ q ∈ Finset.univ.erase q₀, SlashInvariantForm.quotientFunc f q) := by
    rw [IsBoundedAtImInfty, BoundedAtFilter,
      show (1 : ℍ → ℝ) = (fun _ => ∏ _q ∈ Finset.univ.erase q₀, (1 : ℝ)) by ext; simp, Finset.prod_fn]
    exact Asymptotics.IsBigO.finsetProd fun q _ => isBoundedAtImInfty_quotientFunc f q
  obtain ⟨M, A, hMA⟩ := isBoundedAtImInfty_iff.1 hR
  have hF : ∀ τ : ℍ, F τ = f τ * (∏ q ∈ Finset.univ.erase q₀, SlashInvariantForm.quotientFunc f q) τ := by
    intro τ
    rw [ModularForm.coe_norm, ← Finset.mul_prod_erase _ _ (Finset.mem_univ q₀), Pi.mul_apply,
      SlashInvariantForm.quotientFunc_mk, OneMemClass.coe_one, inv_one, SlashAction.slash_one]
  have hcoeff : ∀ n ≤ B, (qExpansion 1 F).coeff n = 0 := by
    intro n hn
    by_contra hne
    have hpos : 0 < ‖(qExpansion 1 F).coeff n‖ := norm_pos_iff.2 hne
    set K := |C| * |M| + 1

    have hbound : ∀ t : ℝ, max 1 A ≤ t → ‖(qExpansion 1 F).coeff n‖ ≤ K * Real.exp (-2 * π * t) := by
      intro t ht
      have ht1 : 1 ≤ t := le_trans (le_max_left _ _) ht
      have htA : A ≤ t := le_trans (le_max_right _ _) ht
      have ht0 : 0 < t := by linarith
      rw [ModularFormClass.qExpansion_coeff_eq_intervalIntegral (f := F) one_pos one_mem_strictPeriods_SL n ht0]
      simp only [Complex.ofReal_one, div_one, one_mul]
      refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := K * Real.exp (-2 * π * t))
        fun u _ => ?_).trans (by simp)
      set τ : ℍ := ⟨u + t * I, by simpa using ht0⟩
      have him : τ.im = t := by simp [τ, UpperHalfPlane.im]
      have h1 := hC τ (by rw [him]; exact ht1)
      have h2 := hMA τ (by rw [him]; exact htA)
      have hq : ‖1 / 𝕢₁ ((u : ℂ) + t * I) ^ n‖ = Real.exp (2 * π * n * t) := by
        rw [norm_div, norm_one, norm_pow, Function.Periodic.norm_qParam, ← Real.exp_nat_mul, one_div,
          ← Real.exp_neg]
        congr 1
        simp
        ring
      change ‖1 / 𝕢₁ ((u : ℂ) + t * I) ^ n * F τ‖ ≤ _
      rw [norm_mul, hq, hF τ, norm_mul, him] at *
      rw [him] at h1
      have hnB : (n : ℝ) ≤ B := by exact_mod_cast hn
      calc Real.exp (2 * π * n * t) * (‖f τ‖ * ‖(∏ q ∈ Finset.univ.erase q₀,
              SlashInvariantForm.quotientFunc f q) τ‖)
          ≤ Real.exp (2 * π * n * t) * ((|C| * Real.exp (-2 * π * (B + 1) * t)) * |M|) := by
            gcongr
            · exact h1.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le)
            · exact h2.trans (le_abs_self M)
        _ = |C| * |M| * (Real.exp (2 * π * n * t) * Real.exp (-2 * π * (B + 1) * t)) := by ring
        _ ≤ |C| * |M| * Real.exp (-2 * π * t) := by
            gcongr
            rw [← Real.exp_add]
            refine Real.exp_le_exp.2 ?_
            have key : 2 * π * n * t + -2 * π * (B + 1) * t = -2 * π * t + 2 * π * t * (n - B) := by ring
            rw [key]
            have : 2 * π * t * ((n : ℝ) - B) ≤ 0 :=
              mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
            linarith
        _ ≤ K * Real.exp (-2 * π * t) := by
            gcongr
            linarith

    have htend : Tendsto (fun t : ℝ => K * Real.exp (-2 * π * t)) atTop (nhds 0) := by
      have : Tendsto (fun t : ℝ => -2 * π * t) atTop atBot :=
        tendsto_id.const_mul_atTop_of_neg (by linarith [Real.pi_pos])
      simpa using (Real.tendsto_exp_atBot.comp this).const_mul K
    obtain ⟨t, ht⟩ := ((htend.eventually (gt_mem_nhds hpos)).and (eventually_ge_atTop (max 1 A))).exists
    exact absurd (hbound t ht.2) (not_le.2 ht.1)
  have hFo : ((B : ℕ) : ℕ∞) < (qExpansion 1 F).order := by
    refine lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self B) (PowerSeries.nat_le_order _ (B + 1) ?_)
    intro i hi
    exact hcoeff i (by omega)
  have hF0 : F = 0 := ModularForm.sturm_bound_levelOne hFo
  have := (ModularForm.norm_eq_zero_iff 𝒮ℒ f).1 hF0
  exact DFunLike.coe_injective (by rw [this]; rfl)

def firstCoeffs (B : ℕ) : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k →ₗ[ℂ] (Fin (B + 1) → ℂ) where
  toFun f i := (qExpansion 1 f).coeff i
  map_add' f g := by
    funext i
    refine qExpansion_coeff_eq_of_hasSum (f + g)
      (b := fun m => (qExpansion 1 f).coeff m + (qExpansion 1 g).coeff m) (fun τ => ?_) i
    have := (hasSum_qExpansion_cusp f τ).add (hasSum_qExpansion_cusp g τ)
    simp only [← add_mul] at this
    exact this
  map_smul' c f := by
    funext i
    refine qExpansion_coeff_eq_of_hasSum (c • f)
      (b := fun m => c * (qExpansion 1 f).coeff m) (fun τ => ?_) i
    have := (hasSum_qExpansion_cusp f τ).mul_left c
    simp only [← mul_assoc] at this
    exact this

instance finiteDimensional_cuspForm : FiniteDimensional ℂ (CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k) := by
  refine Module.Finite.of_injective (firstCoeffs (N := N) (k := k) (sturmBoundGamma0 N k)) ?_
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro f hf
  refine eq_zero_of_coeff_le_sturmBound f fun n hn => ?_
  have := congrFun hf ⟨n, by omega⟩
  exact this

end GL2Classical

end

end GroundTheory.Automorphic
