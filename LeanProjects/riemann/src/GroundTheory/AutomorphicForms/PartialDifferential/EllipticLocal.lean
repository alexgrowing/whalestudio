import Mathlib
import GroundTheory.AutomorphicForms.PartialDifferential.EllipticOperators

namespace GroundTheory.Automorphic.Sobolev

open TemperedDistribution MeasureTheory FourierTransform LineDeriv
open scoped SchwartzMap ENNReal ContDiff

noncomputable section

set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem one_le_sqrt_one_add_norm_sq (ξ : E) : 1 ≤ Real.sqrt (1 + ‖ξ‖ ^ 2) := by
  rw [Real.one_le_sqrt]; nlinarith [sq_nonneg ‖ξ‖]

theorem norm_le_sqrt_one_add_norm_sq (ξ : E) : ‖ξ‖ ≤ Real.sqrt (1 + ‖ξ‖ ^ 2) :=
  Real.le_sqrt_of_sq_le (by linarith)

theorem rpow_eq_sqrt_pow (ξ : E) (k : ℕ) :
    (1 + ‖ξ‖ ^ 2) ^ ((k : ℝ) / 2) = Real.sqrt (1 + ‖ξ‖ ^ 2) ^ k := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast ((1 + ‖ξ‖ ^ 2) ^ (1 / 2 : ℝ)) k,
    ← Real.rpow_mul (by positivity)]
  congr 1; ring

theorem norm_le_of_mul_sqrt_pow_le {f : E → ℂ} {C : ℝ} {k : ℕ}
    (h : ∀ ξ, ‖f ξ‖ * Real.sqrt (1 + ‖ξ‖ ^ 2) ^ k ≤ C) (ξ : E) :
    ‖f ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (-(k : ℝ) / 2) := by
  have hp : 0 < Real.sqrt (1 + ‖ξ‖ ^ 2) ^ k :=
    pow_pos (lt_of_lt_of_le one_pos (one_le_sqrt_one_add_norm_sq ξ)) k
  rw [neg_div, Real.rpow_neg (by positivity), rpow_eq_sqrt_pow, ← div_eq_mul_inv,
    le_div_iff₀ hp]
  exact h ξ

section Symbols

variable {ι : Type*} [Fintype ι] {m : ℕ} (c : ι → ℂ) (w : ι → Fin m → E)

def symb0 : E → ℂ := fun ξ ↦ (2 * Real.pi * Complex.I) ^ m * prinSymb c w ξ

theorem parametrixSymbol_hasTemperateGrowth : (symb0 c w).HasTemperateGrowth :=
  constSymb_hasTemperateGrowth w c

theorem constOp_eq_symb0 : constOp w c = fourierMultiplierCLM ℂ (symb0 c w) :=
  constOp_eq_fourierMultiplier w c

def rhoSymb (μ : ℝ) : E → ℂ := fun ξ ↦ weight (-2) ((Real.sqrt μ : ℂ) * symb0 c w ξ)

theorem rhoSymb_eq {μ : ℝ} (hμ : 0 ≤ μ) (ξ : E) :
    rhoSymb c w μ ξ = (((1 + μ * ‖symb0 c w ξ‖ ^ 2)⁻¹ : ℝ) : ℂ) := by
  unfold rhoSymb weight
  congr 1
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt hμ, show (-2 : ℝ) / 2 = -1 by norm_num, Real.rpow_neg_one]

theorem rhoSymb_hasTemperateGrowth (μ : ℝ) : (rhoSymb c w μ).HasTemperateGrowth :=
  (weight_hasTemperateGrowth (E := ℂ) (-2)).comp
    ((Function.HasTemperateGrowth.const _).mul (parametrixSymbol_hasTemperateGrowth c w))

def qSymb (μ : ℝ) : E → ℂ := fun ξ ↦ (μ : ℂ) * starRingEnd ℂ (symb0 c w ξ) * rhoSymb c w μ ξ

theorem qSymb_hasTemperateGrowth (μ : ℝ) : (qSymb c w μ).HasTemperateGrowth := by
  have h : (fun ξ ↦ starRingEnd ℂ (symb0 c w ξ)).HasTemperateGrowth :=
    (Complex.conjCLE.hasTemperateGrowth).comp (parametrixSymbol_hasTemperateGrowth c w)
  exact ((Function.HasTemperateGrowth.const _).mul h).mul (rhoSymb_hasTemperateGrowth c w μ)

def qNSymb (μ : ℝ) (N : ℕ) : E → ℂ :=
  fun ξ ↦ qSymb c w μ ξ * ∑ j ∈ Finset.range N, rhoSymb c w μ ξ ^ j

def rNSymb (μ : ℝ) (N : ℕ) : E → ℂ := fun ξ ↦ rhoSymb c w μ ξ ^ N

theorem qNSymb_hasTemperateGrowth (μ : ℝ) (N : ℕ) : (qNSymb c w μ N).HasTemperateGrowth :=
  (qSymb_hasTemperateGrowth c w μ).mul
    (Function.HasTemperateGrowth.sum fun j _ ↦ (rhoSymb_hasTemperateGrowth c w μ).pow j)

theorem rNSymb_hasTemperateGrowth (μ : ℝ) (N : ℕ) : (rNSymb c w μ N).HasTemperateGrowth :=
  (rhoSymb_hasTemperateGrowth c w μ).pow N

theorem parametrixSymbol_mul_inverseSymbol {μ : ℝ} (hμ : 0 ≤ μ) (ξ : E) :
    symb0 c w ξ * qSymb c w μ ξ = 1 - rhoSymb c w μ ξ := by
  rw [qSymb, rhoSymb_eq c w hμ]
  have hpos : (0 : ℝ) < 1 + μ * ‖symb0 c w ξ‖ ^ 2 := by positivity
  have hmc : symb0 c w ξ * starRingEnd ℂ (symb0 c w ξ) = ((‖symb0 c w ξ‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  calc symb0 c w ξ * ((μ : ℂ) * starRingEnd ℂ (symb0 c w ξ) *
        (((1 + μ * ‖symb0 c w ξ‖ ^ 2)⁻¹ : ℝ) : ℂ))
      = (μ : ℂ) * (symb0 c w ξ * starRingEnd ℂ (symb0 c w ξ)) *
          (((1 + μ * ‖symb0 c w ξ‖ ^ 2)⁻¹ : ℝ) : ℂ) := by ring
    _ = (((μ * ‖symb0 c w ξ‖ ^ 2) * (1 + μ * ‖symb0 c w ξ‖ ^ 2)⁻¹ : ℝ) : ℂ) := by
        rw [hmc]; push_cast; ring
    _ = ((1 - (1 + μ * ‖symb0 c w ξ‖ ^ 2)⁻¹ : ℝ) : ℂ) := by
        congr 1; field_simp; ring
    _ = _ := by push_cast; ring

theorem parametrixSymbol_mul_inverseSymbolOfOrder {μ : ℝ} (hμ : 0 ≤ μ) (N : ℕ) (ξ : E) :
    symb0 c w ξ * qNSymb c w μ N ξ = 1 - rNSymb c w μ N ξ := by
  rw [qNSymb, ← mul_assoc, parametrixSymbol_mul_inverseSymbol c w hμ, rNSymb, mul_neg_geom_sum]

theorem norm_rhoSymb {μ : ℝ} (hμ : 0 ≤ μ) (ξ : E) :
    ‖rhoSymb c w μ ξ‖ = (1 + μ * ‖symb0 c w ξ‖ ^ 2)⁻¹ := by
  rw [rhoSymb_eq c w hμ, Complex.norm_real, Real.norm_of_nonneg (by positivity)]

theorem norm_rhoSymb_le_one {μ : ℝ} (hμ : 0 ≤ μ) (ξ : E) : ‖rhoSymb c w μ ξ‖ ≤ 1 := by
  rw [norm_rhoSymb c w hμ]
  exact inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg ‖symb0 c w ξ‖])

theorem norm_qSymb {μ : ℝ} (hμ : 0 ≤ μ) (ξ : E) :
    ‖qSymb c w μ ξ‖ = μ * ‖symb0 c w ξ‖ * (1 + μ * ‖symb0 c w ξ‖ ^ 2)⁻¹ := by
  rw [qSymb, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hμ, Complex.norm_conj,
    norm_rhoSymb c w hμ]

theorem norm_qSymb_le {μ : ℝ} (hμ : 0 ≤ μ) (ξ : E) :
    ‖qSymb c w μ ξ‖ ≤ μ * ‖symb0 c w ξ‖ := by
  rw [norm_qSymb c w hμ]
  have := norm_rhoSymb_le_one c w hμ ξ
  rw [norm_rhoSymb c w hμ] at this
  calc μ * ‖symb0 c w ξ‖ * (1 + μ * ‖symb0 c w ξ‖ ^ 2)⁻¹ ≤ μ * ‖symb0 c w ξ‖ * 1 := by
        gcongr
    _ = _ := mul_one _

theorem norm_qSymb_mul_le {μ : ℝ} (hμ : 0 ≤ μ) (ξ : E) :
    ‖qSymb c w μ ξ‖ * ‖symb0 c w ξ‖ ≤ 1 := by
  rw [norm_qSymb c w hμ]
  have hpos : (0 : ℝ) < 1 + μ * ‖symb0 c w ξ‖ ^ 2 := by positivity
  rw [show μ * ‖symb0 c w ξ‖ * (1 + μ * ‖symb0 c w ξ‖ ^ 2)⁻¹ * ‖symb0 c w ξ‖ =
    (μ * ‖symb0 c w ξ‖ ^ 2) / (1 + μ * ‖symb0 c w ξ‖ ^ 2) by field_simp]
  rw [div_le_one hpos]; linarith

theorem norm_qNSymb_le {μ : ℝ} (hμ : 0 ≤ μ) (N : ℕ) (ξ : E) :
    ‖qNSymb c w μ N ξ‖ ≤ N * ‖qSymb c w μ ξ‖ := by
  rw [qNSymb, norm_mul, mul_comm]
  gcongr
  refine (norm_sum_le _ _).trans ?_
  calc ∑ j ∈ Finset.range N, ‖rhoSymb c w μ ξ ^ j‖ ≤ ∑ j ∈ Finset.range N, (1 : ℝ) := by
        gcongr with j
        rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (norm_rhoSymb_le_one c w hμ ξ)
    _ = N := by simp

end Symbols

section Bounds

variable {ι : Type*} [Fintype ι] {m : ℕ} (c : ι → ℂ) (w : ι → Fin m → E) {cl Cu : ℝ}

theorem sqrt_one_add_norm_sq_le_two_mul {ξ : E} (h : 1 ≤ ‖ξ‖) :
    Real.sqrt (1 + ‖ξ‖ ^ 2) ≤ 2 * ‖ξ‖ := by
  rw [Real.sqrt_le_iff]; constructor
  · positivity
  · nlinarith

theorem sqrt_one_add_norm_sq_le_two {ξ : E} (h : ‖ξ‖ ≤ 1) : Real.sqrt (1 + ‖ξ‖ ^ 2) ≤ 2 := by
  rw [Real.sqrt_le_iff]; constructor
  · norm_num
  · nlinarith [norm_nonneg ξ]

variable (hcl : 0 < cl) (hCu : 0 ≤ Cu) (hlow : ∀ ξ, cl * ‖ξ‖ ^ m ≤ ‖symb0 c w ξ‖)
  (hup : ∀ ξ, ‖symb0 c w ξ‖ ≤ Cu * ‖ξ‖ ^ m)
include hcl hCu hlow hup

theorem qSymb_mul_sqrt_pow_le {μ : ℝ} (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) (ξ : E) :
    ‖qSymb c w μ ξ‖ * Real.sqrt (1 + ‖ξ‖ ^ 2) ^ m ≤ 2 ^ m * (cl⁻¹ + Cu) := by
  have hq0 := norm_nonneg (qSymb c w μ ξ)
  rcases le_or_gt 1 ‖ξ‖ with h | h
  · have hS := pow_le_pow_left₀ (Real.sqrt_nonneg _) (sqrt_one_add_norm_sq_le_two_mul h) m
    have hξm : 0 < ‖ξ‖ ^ m := pow_pos (by linarith) m
    have hp : ‖ξ‖ ^ m ≤ ‖symb0 c w ξ‖ / cl := by rw [le_div_iff₀ hcl, mul_comm]; exact hlow ξ
    calc ‖qSymb c w μ ξ‖ * Real.sqrt (1 + ‖ξ‖ ^ 2) ^ m ≤ ‖qSymb c w μ ξ‖ * (2 * ‖ξ‖) ^ m := by
          gcongr
      _ = 2 ^ m * (‖qSymb c w μ ξ‖ * ‖ξ‖ ^ m) := by rw [mul_pow]; ring
      _ ≤ 2 ^ m * (‖qSymb c w μ ξ‖ * (‖symb0 c w ξ‖ / cl)) := by gcongr
      _ = 2 ^ m * ((‖qSymb c w μ ξ‖ * ‖symb0 c w ξ‖) * cl⁻¹) := by ring
      _ ≤ 2 ^ m * (1 * cl⁻¹) := by
          gcongr; exact norm_qSymb_mul_le c w hμ0 ξ
      _ ≤ 2 ^ m * (cl⁻¹ + Cu) := by gcongr; linarith
  · have hS := pow_le_pow_left₀ (Real.sqrt_nonneg _) (sqrt_one_add_norm_sq_le_two h.le) m
    have hξm : ‖ξ‖ ^ m ≤ 1 := pow_le_one₀ (norm_nonneg _) h.le
    have hq : ‖qSymb c w μ ξ‖ ≤ Cu := by
      calc ‖qSymb c w μ ξ‖ ≤ μ * ‖symb0 c w ξ‖ := norm_qSymb_le c w hμ0 ξ
        _ ≤ 1 * (Cu * ‖ξ‖ ^ m) := by gcongr; exact hup ξ
        _ ≤ 1 * (Cu * 1) := by gcongr
        _ = Cu := by ring
    calc ‖qSymb c w μ ξ‖ * Real.sqrt (1 + ‖ξ‖ ^ 2) ^ m ≤ Cu * 2 ^ m := by gcongr
      _ ≤ 2 ^ m * (cl⁻¹ + Cu) := by
          rw [mul_comm]; gcongr; linarith [inv_pos.2 hcl]

theorem qNSymb_bound {μ : ℝ} (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) (N : ℕ) (ξ : E) :
    ‖qNSymb c w μ N ξ‖ ≤ (N * (2 ^ m * (cl⁻¹ + Cu))) * (1 + ‖ξ‖ ^ 2) ^ (-(m : ℝ) / 2) := by
  refine norm_le_of_mul_sqrt_pow_le (fun ξ ↦ ?_) ξ
  calc ‖qNSymb c w μ N ξ‖ * Real.sqrt (1 + ‖ξ‖ ^ 2) ^ m
      ≤ (N * ‖qSymb c w μ ξ‖) * Real.sqrt (1 + ‖ξ‖ ^ 2) ^ m := by
        gcongr; exact norm_qNSymb_le c w hμ0 N ξ
    _ = N * (‖qSymb c w μ ξ‖ * Real.sqrt (1 + ‖ξ‖ ^ 2) ^ m) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (qSymb_mul_sqrt_pow_le c w hcl hCu hlow hup hμ0 hμ1 ξ)
        (Nat.cast_nonneg N)

theorem exists_qSymb_small (hm : 1 ≤ m) {ε : ℝ} (hε : 0 < ε) :
    ∃ μ : ℝ, 0 < μ ∧ μ ≤ 1 ∧ ∀ ξ : E, ‖qSymb c w μ ξ‖ * Real.sqrt (1 + ‖ξ‖ ^ 2) ^ (m - 1) ≤ ε := by
  set CQ := 2 ^ m * (cl⁻¹ + Cu)
  have hCQ : 0 < CQ := by positivity
  set lam := max 1 (2 * CQ / ε)
  have hlam1 : 1 ≤ lam := le_max_left _ _
  set S0 := Real.sqrt (1 + lam ^ 2)
  have hS01 : 1 ≤ S0 := by rw [Real.one_le_sqrt]; nlinarith
  set D := (Cu + 1) * S0 ^ (2 * m)
  have hD : 0 < D := by positivity
  refine ⟨min 1 (ε / (2 * D)), lt_min one_pos (by positivity), min_le_left _ _, fun ξ ↦ ?_⟩
  set μ := min 1 (ε / (2 * D))
  have hμ0 : 0 ≤ μ := le_min zero_le_one (by positivity)
  have hμ1 : μ ≤ 1 := min_le_left _ _
  set S := Real.sqrt (1 + ‖ξ‖ ^ 2)
  have hS1 : 1 ≤ S := one_le_sqrt_one_add_norm_sq ξ
  have hq0 := norm_nonneg (qSymb c w μ ξ)
  rcases le_or_gt lam ‖ξ‖ with h | h
  · have hSl : lam ≤ S := h.trans (norm_le_sqrt_one_add_norm_sq ξ)
    have key := qSymb_mul_sqrt_pow_le c w hcl hCu hlow hup hμ0 hμ1 ξ
    have e : S ^ m = S ^ (m - 1) * S := by rw [← pow_succ, Nat.sub_add_cancel hm]
    have hSpos : 0 < S := by linarith
    have h1 : ‖qSymb c w μ ξ‖ * S ^ (m - 1) ≤ CQ / S := by
      rw [le_div_iff₀ hSpos]
      calc ‖qSymb c w μ ξ‖ * S ^ (m - 1) * S = ‖qSymb c w μ ξ‖ * S ^ m := by rw [e]; ring
        _ ≤ CQ := key
    calc ‖qSymb c w μ ξ‖ * S ^ (m - 1) ≤ CQ / S := h1
      _ ≤ CQ / lam := by gcongr
      _ ≤ CQ / (2 * CQ / ε) := by gcongr; exact le_max_right _ _
      _ = ε / 2 := by field_simp
      _ ≤ ε := by linarith
  · have hSS0 : S ≤ S0 := Real.sqrt_le_sqrt (by nlinarith [norm_nonneg ξ])
    have hξS : ‖ξ‖ ^ m ≤ S ^ m := pow_le_pow_left₀ (norm_nonneg _) (norm_le_sqrt_one_add_norm_sq ξ) m
    have hq : ‖qSymb c w μ ξ‖ ≤ μ * (Cu * S ^ m) := by
      calc ‖qSymb c w μ ξ‖ ≤ μ * ‖symb0 c w ξ‖ := norm_qSymb_le c w hμ0 ξ
        _ ≤ μ * (Cu * ‖ξ‖ ^ m) := by gcongr; exact hup ξ
        _ ≤ μ * (Cu * S ^ m) := by gcongr
    calc ‖qSymb c w μ ξ‖ * S ^ (m - 1) ≤ μ * (Cu * S ^ m) * S ^ (m - 1) := by gcongr
      _ = μ * Cu * S ^ (m + (m - 1)) := by rw [pow_add]; ring
      _ ≤ μ * (Cu + 1) * S0 ^ (2 * m) := by
          gcongr
          · linarith
          · calc S ^ (m + (m - 1)) ≤ S ^ (2 * m) := pow_le_pow_right₀ hS1 (by omega)
              _ ≤ S0 ^ (2 * m) := pow_le_pow_left₀ (by linarith) hSS0 _
      _ = μ * D := by ring
      _ ≤ ε / (2 * D) * D := by gcongr; exact min_le_right _ _
      _ = ε / 2 := by field_simp
      _ ≤ ε := by linarith

theorem rhoSymb_mul_sqrt_pow_le {μ : ℝ} (hμ : 0 < μ) (ξ : E) :
    ‖rhoSymb c w μ ξ‖ * Real.sqrt (1 + ‖ξ‖ ^ 2) ^ (2 * m) ≤ 4 ^ m * (1 + (μ * cl ^ 2)⁻¹) := by
  have hr0 := norm_nonneg (rhoSymb c w μ ξ)
  have hK : 4 ^ m ≤ 4 ^ m * (1 + (μ * cl ^ 2)⁻¹) := by
    have : 0 ≤ (μ * cl ^ 2)⁻¹ := by positivity
    nlinarith [pow_pos (by norm_num : (0:ℝ) < 4) m]
  rcases le_or_gt 1 ‖ξ‖ with h | h
  · have hS := pow_le_pow_left₀ (Real.sqrt_nonneg _) (sqrt_one_add_norm_sq_le_two_mul h) (2 * m)
    have hξ : 0 < ‖ξ‖ := by linarith
    have hp2 : (cl * ‖ξ‖ ^ m) ^ 2 ≤ ‖symb0 c w ξ‖ ^ 2 :=
      pow_le_pow_left₀ (by positivity) (hlow ξ) 2
    have hpos : 0 < μ * cl ^ 2 * ‖ξ‖ ^ (2 * m) := by positivity
    have hρ : ‖rhoSymb c w μ ξ‖ ≤ (μ * cl ^ 2 * ‖ξ‖ ^ (2 * m))⁻¹ := by
      rw [norm_rhoSymb c w hμ.le]
      apply inv_anti₀ hpos
      have : μ * cl ^ 2 * ‖ξ‖ ^ (2 * m) = μ * (cl * ‖ξ‖ ^ m) ^ 2 := by ring
      rw [this]; nlinarith
    calc ‖rhoSymb c w μ ξ‖ * Real.sqrt (1 + ‖ξ‖ ^ 2) ^ (2 * m)
        ≤ (μ * cl ^ 2 * ‖ξ‖ ^ (2 * m))⁻¹ * (2 * ‖ξ‖) ^ (2 * m) := by gcongr
      _ = 4 ^ m * (μ * cl ^ 2)⁻¹ := by
          rw [mul_pow, pow_mul 2 2 m]; field_simp; norm_num
      _ ≤ 4 ^ m * (1 + (μ * cl ^ 2)⁻¹) := by gcongr; linarith
  · have hS := pow_le_pow_left₀ (Real.sqrt_nonneg _) (sqrt_one_add_norm_sq_le_two h.le) (2 * m)
    calc ‖rhoSymb c w μ ξ‖ * Real.sqrt (1 + ‖ξ‖ ^ 2) ^ (2 * m) ≤ 1 * 2 ^ (2 * m) := by
          gcongr; exact norm_rhoSymb_le_one c w hμ.le ξ
      _ = 4 ^ m := by rw [one_mul, pow_mul]; norm_num
      _ ≤ _ := hK

theorem rNSymb_bound {μ : ℝ} (hμ : 0 < μ) (N : ℕ) (ξ : E) :
    ‖rNSymb c w μ N ξ‖ ≤ (4 ^ m * (1 + (μ * cl ^ 2)⁻¹)) ^ N *
      (1 + ‖ξ‖ ^ 2) ^ (-((2 * m * N : ℕ) : ℝ) / 2) := by
  refine norm_le_of_mul_sqrt_pow_le (fun ξ ↦ ?_) ξ
  rw [rNSymb, norm_pow, show 2 * m * N = (2 * m) * N by ring, pow_mul, ← mul_pow]
  exact pow_le_pow_left₀ (by positivity) (rhoSymb_mul_sqrt_pow_le c w hcl hCu hlow hup hμ ξ) N

end Bounds

def bumpR (x₀ : E) {r : ℝ} (hr : 0 < r) : ContDiffBump x₀ := ⟨r, 2 * r, hr, by linarith⟩

def bump (x₀ : E) {r : ℝ} (hr : 0 < r) : 𝓢(E, ℂ) :=
  have h₁ : HasCompactSupport (Complex.ofRealCLM ∘ (bumpR x₀ hr : E → ℝ)) :=
    (bumpR x₀ hr).hasCompactSupport.comp_left rfl
  have h₂ : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ (bumpR x₀ hr : E → ℝ)) :=
    Complex.ofRealCLM.contDiff.comp (bumpR x₀ hr).contDiff
  h₁.toSchwartzMap h₂

theorem bump_apply (x₀ : E) {r : ℝ} (hr : 0 < r) (x : E) :
    bump x₀ hr x = ((bumpR x₀ hr x : ℝ) : ℂ) := rfl

theorem bump_eq_one (x₀ : E) {r : ℝ} (hr : 0 < r) {x : E} (hx : x ∈ Metric.closedBall x₀ r) :
    bump x₀ hr x = 1 := by
  rw [bump_apply, (bumpR x₀ hr).one_of_mem_closedBall hx, Complex.ofReal_one]

theorem norm_bump_le (x₀ : E) {r : ℝ} (hr : 0 < r) (x : E) : ‖bump x₀ hr x‖ ≤ 1 := by
  rw [bump_apply, Complex.norm_real, Real.norm_of_nonneg (bumpR x₀ hr).nonneg]
  exact (bumpR x₀ hr).le_one

theorem tsupport_bump (x₀ : E) {r : ℝ} (hr : 0 < r) :
    tsupport (bump x₀ hr : E → ℂ) ⊆ Metric.closedBall x₀ (2 * r) := by
  have : (bump x₀ hr : E → ℂ) = Complex.ofRealCLM ∘ (bumpR x₀ hr : E → ℝ) := rfl
  rw [this]
  refine (tsupport_comp_subset (g := Complex.ofRealCLM) (by simp) _).trans ?_
  rw [(bumpR x₀ hr).tsupport_eq]; rfl

theorem bump_eq_zero (x₀ : E) {r : ℝ} (hr : 0 < r) {x : E} (hx : x ∉ Metric.closedBall x₀ (2 * r)) :
    bump x₀ hr x = 0 :=
  image_eq_zero_of_notMem_tsupport fun h ↦ hx (tsupport_bump x₀ hr h)

theorem smulLeftCLM_eq_self {g : E → ℂ} (hg : g.HasTemperateGrowth) {V U : Set E} (hV : IsOpen V)
    (hg1 : ∀ x ∈ V, g x = 1) (hVU : Vᶜ ⊆ U) {z : 𝓢'(E, ℂ)} (hz : Distribution.IsVanishingOn z U) :
    smulLeftCLM ℂ g z = z := by
  have h1 : (fun x ↦ g x - 1).HasTemperateGrowth := hg.sub (Function.HasTemperateGrowth.const 1)
  have hts : tsupport (fun x ↦ g x - 1) ⊆ U := by
    refine (closure_minimal ?_ hV.isClosed_compl).trans hVU
    intro x hx hxV
    exact hx (by simp [hg1 x hxV])
  have h0 := smulLeftCLM_eq_zero_of_isVanishingOn h1 hz hts
  have e : smulLeftCLM ℂ (fun x ↦ g x - 1) z = smulLeftCLM ℂ g z - z := by
    rw [show (fun x ↦ g x - 1) = g - fun _ ↦ (1 : ℂ) from rfl,
      smulLeftCLM_sub hg (Function.HasTemperateGrowth.const 1), sub_apply, smulLeftCLM_const,
      one_smul]
  rw [e, sub_eq_zero] at h0
  exact h0

theorem bump_smul_eq_self (x₀ : E) {r ρ : ℝ} (hr : 0 < r) (hρ : ρ < r) {z : 𝓢'(E, ℂ)}
    (hz : Distribution.IsVanishingOn z (Metric.closedBall x₀ ρ)ᶜ) :
    smulLeftCLM ℂ (bump x₀ hr : E → ℂ) z = z := by
  refine smulLeftCLM_eq_self (bump x₀ hr).hasTemperateGrowth Metric.isOpen_ball
    (fun x hx ↦ bump_eq_one x₀ hr (Metric.ball_subset_closedBall hx)) ?_ hz
  intro x hx
  simp only [Set.mem_compl_iff, Metric.mem_ball, not_lt, Metric.mem_closedBall, not_le] at hx ⊢
  linarith

theorem smulLeftCLM_schwartz_mul (χ f : 𝓢(E, ℂ)) (v : 𝓢'(E, ℂ)) :
    smulLeftCLM ℂ ((SchwartzMap.smulLeftCLM ℂ (χ : E → ℂ) f : 𝓢(E, ℂ)) : E → ℂ) v =
      smulLeftCLM ℂ (χ : E → ℂ) (smulLeftCLM ℂ (f : E → ℂ) v) := by
  ext φ
  simp only [smulLeftCLM_apply_apply]
  congr 1; ext x
  simp only [SchwartzMap.smulLeftCLM_apply_apply χ.hasTemperateGrowth,
    SchwartzMap.smulLeftCLM_apply_apply f.hasTemperateGrowth,
    SchwartzMap.smulLeftCLM_apply_apply (SchwartzMap.smulLeftCLM ℂ (χ : E → ℂ) f).hasTemperateGrowth,
    smul_eq_mul]
  ring

theorem smulLeftCLM_schwartz_sub_smul (f g : 𝓢(E, ℂ)) (c : ℂ) (v : 𝓢'(E, ℂ)) :
    smulLeftCLM ℂ ((f - c • g : 𝓢(E, ℂ)) : E → ℂ) v =
      smulLeftCLM ℂ (f : E → ℂ) v - c • smulLeftCLM ℂ (g : E → ℂ) v := by
  ext φ
  simp only [smulLeftCLM_apply_apply, sub_apply, smul_apply]
  rw [← map_smul, ← map_sub]
  congr 1; ext x
  simp only [SchwartzMap.smulLeftCLM_apply_apply f.hasTemperateGrowth,
    SchwartzMap.smulLeftCLM_apply_apply g.hasTemperateGrowth,
    SchwartzMap.smulLeftCLM_apply_apply (f - c • g).hasTemperateGrowth, smul_eq_mul,
    sub_apply, smul_apply]
  ring

section Local

variable {m n : ℕ} (a : Fin n → 𝓢(E, ℂ)) (w : Fin n → Fin m → E) (N : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ))
  (x₀ : E)

def locCoeff {δ : ℝ} (hδ : 0 < δ) (i : Fin n) : 𝓢(E, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (bump x₀ hδ : E → ℂ) (a i) - a i x₀ • bump x₀ hδ

def locM {δ : ℝ} (hδ : 0 < δ) : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ) :=
  prinOp (locCoeff a x₀ hδ) w + smulLeftCLM ℂ (bump x₀ hδ : E → ℂ) ∘L N

def P0 : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ) := constOp w (fun i ↦ a i x₀)

theorem norm_locCoeff_le {δ : ℝ} (hδ : 0 < δ) (i : Fin n) {η : ℝ} (hη : 0 ≤ η)
    (h : ∀ y ∈ Metric.closedBall x₀ (2 * δ), ‖a i y - a i x₀‖ ≤ η) (x : E) :
    ‖locCoeff a x₀ hδ i x‖ ≤ η := by
  have e : locCoeff a x₀ hδ i x = bump x₀ hδ x * (a i x - a i x₀) := by
    simp only [locCoeff, sub_apply, smul_apply,
      SchwartzMap.smulLeftCLM_apply_apply (bump x₀ hδ).hasTemperateGrowth, smul_eq_mul]
    ring
  rw [e, norm_mul]
  by_cases hx : x ∈ Metric.closedBall x₀ (2 * δ)
  · calc ‖bump x₀ hδ x‖ * ‖a i x - a i x₀‖ ≤ 1 * η :=
          mul_le_mul (norm_bump_le x₀ hδ x) (h x hx) (norm_nonneg _) zero_le_one
      _ = η := one_mul η
  · rw [bump_eq_zero x₀ hδ hx, norm_zero, zero_mul]; exact hη

theorem prinOp_add_apply_eq (hNl : IsLocal N) {δ ρ : ℝ} (hδ : 0 < δ) (hρ : ρ < δ) {u : 𝓢'(E, ℂ)}
    (hu : Distribution.IsVanishingOn u (Metric.closedBall x₀ ρ)ᶜ) :
    (prinOp a w + N) u = P0 a w x₀ u + locM a w N x₀ hδ u := by
  have hU : IsOpen (Metric.closedBall x₀ ρ)ᶜ := Metric.isClosed_closedBall.isOpen_compl
  have hv : ∀ i, Distribution.IsVanishingOn (iteratedLineDerivOpCLM ℂ 𝓢'(E, ℂ) (w i) u)
      (Metric.closedBall x₀ ρ)ᶜ := fun i ↦ isLocal_iteratedLineDeriv (w i) _ hU u hu
  simp only [iteratedLineDerivOpCLM_apply] at hv
  simp only [add_apply, locM, P0, prinOp, constOp, sum_apply,
    ContinuousLinearMap.comp_apply, smul_apply, iteratedLineDerivOpCLM_apply]
  rw [bump_smul_eq_self x₀ hδ hρ (hNl _ hU u hu), ← add_assoc, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [locCoeff, smulLeftCLM_schwartz_sub_smul, smulLeftCLM_schwartz_mul,
    bump_smul_eq_self x₀ hδ hρ (isLocal_smulLeft (a i).hasTemperateGrowth _ hU _ (hv i)),
    bump_smul_eq_self x₀ hδ hρ (hv i)]
  abel

end Local

def OpBound (A : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ)) (s t C : ℝ) : Prop :=
  ∀ u : 𝓢'(E, ℂ), MemSobolev s 2 u → sob t (A u) ≤ ENNReal.ofReal C * sob s u

namespace OpBound

variable {A B : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ)} {s t r C D : ℝ}

theorem memSobolev (h : OpBound A s t C) {u : 𝓢'(E, ℂ)} (hu : MemSobolev s 2 u) :
    MemSobolev t 2 (A u) :=
  memSobolev_of_sob_le ENNReal.ofReal_ne_top (h u hu) hu

theorem comp (hA : OpBound A t r C) (hB : OpBound B s t D) (hC : 0 ≤ C) :
    OpBound (A ∘L B) s r (C * D) := fun u hu ↦ by
  rw [ContinuousLinearMap.comp_apply, ENNReal.ofReal_mul hC, mul_assoc]
  exact (hA _ (hB.memSobolev hu)).trans (mul_le_mul_right (hB u hu) _)

theorem add (hA : OpBound A s t C) (hB : OpBound B s t D) (hC : 0 ≤ C) (hD : 0 ≤ D) :
    OpBound (A + B) s t (C + D) := fun u hu ↦ by
  rw [add_apply, ENNReal.ofReal_add hC hD, add_mul]
  exact (sob_add_le _ _).trans (add_le_add (hA u hu) (hB u hu))

theorem mono (hA : OpBound A s t C) (hCD : C ≤ D) : OpBound A s t D := fun u hu ↦
  (hA u hu).trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal hCD) _)

theorem congr_idx (hA : OpBound A s t C) {s' t' : ℝ} (hs : s' = s) (ht : t' = t) :
    OpBound A s' t' C := by subst hs ht; exact hA

theorem sum {ι : Type*} (S : Finset ι) {A : ι → 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ)} {C : ι → ℝ}
    (hC : ∀ i ∈ S, 0 ≤ C i) (h : ∀ i ∈ S, OpBound (A i) s t (C i)) :
    OpBound (∑ i ∈ S, A i) s t (∑ i ∈ S, C i) := by
  classical
  induction S using Finset.induction_on with
  | empty => intro u _; simp [sob_zero]
  | insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a S)).add
      (ih (fun i hi ↦ hC i (Finset.mem_insert_of_mem hi)) fun i hi ↦ h i (Finset.mem_insert_of_mem hi))
      (hC a (Finset.mem_insert_self a S)) (Finset.sum_nonneg fun i hi ↦ hC i (Finset.mem_insert_of_mem hi))

end OpBound

theorem opBound_fourierMultiplier {g : E → ℂ} (hg : g.HasTemperateGrowth) {C s t : ℝ}
    (hC : ∀ ξ, ‖g ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((s - t) / 2)) : OpBound (fourierMultiplierCLM ℂ g) s t C :=
  fun _ hu ↦ sob_fourierMultiplier_le hg hC hu

theorem opBound_iteratedLineDeriv {k : ℕ} (w : Fin k → E) (s : ℝ) :
    OpBound (iteratedLineDerivOpCLM ℂ 𝓢'(E, ℂ) w) s (s - k) (∏ j, (2 * Real.pi * ‖w j‖)) := by
  intro u hu
  rw [iteratedLineDerivOpCLM_apply, iteratedLineDeriv_eq_fourierMultiplier]
  refine sob_fourierMultiplier_le (derivSymb_hasTemperateGrowth w) (fun ξ ↦ ?_) hu
  rw [show (s - (s - k)) / 2 = (k : ℝ) / 2 by ring, rpow_eq_sqrt_pow]
  refine (norm_derivSymb_le w ξ).trans ?_
  gcongr
  exact norm_le_sqrt_one_add_norm_sq ξ

theorem opBound_smulLeft (χ : 𝓢(E, ℂ)) (s : ℝ) :
    OpBound (smulLeftCLM ℂ (χ : E → ℂ)) s s (mulConst s χ) :=
  fun _ hu ↦ sob_smulLeft_le χ s hu

theorem opBound_mulPrin (χ : 𝓢(E, ℂ)) {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ x, ‖χ x‖ ≤ M) (s : ℝ) :
    OpBound (mulPrin χ s) s s M :=
  fun _ hu ↦ sob_mulPrin_le χ hM0 hM s hu

theorem exists_add_eq_of_opBound {K : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ)} {s : ℝ} (hK : OpBound K s s (1 / 2))
    {z : 𝓢'(E, ℂ)} (hz : MemSobolev s 2 z) : ∃ v, MemSobolev s 2 v ∧ v + K v = z := by
  have hmem : ∀ v : SobolevSpace E ℂ s, MemSobolev s 2 (z - K (SobolevSpace.toDistribution v)) :=
    fun v ↦ (SobolevSpace.exists_toDistribution_eq_iff _).1
      ⟨SobolevSpace.mk z hz - SobolevSpace.mk _ (hK.memSobolev (SobolevSpace.memSobolev_toDistribution v)),
        by simp⟩
  let f : SobolevSpace E ℂ s → SobolevSpace E ℂ s := fun v ↦ SobolevSpace.mk _ (hmem v)
  have hf : ContractingWith (1 / 2 : NNReal) f := by
    refine ⟨by rw [← NNReal.coe_lt_coe]; norm_num, LipschitzWith.of_dist_le_mul fun v v' ↦ ?_⟩
    rw [dist_eq_norm, dist_eq_norm]
    have e : f v - f v' = SobolevSpace.mk (K (SobolevSpace.toDistribution (v' - v)))
        (hK.memSobolev (SobolevSpace.memSobolev_toDistribution _)) := by
      apply SobolevSpace.toDistribution_injective
      simp [f, map_sub]
    rw [e]
    have h := hK _ (SobolevSpace.memSobolev_toDistribution (v' - v))
    rw [sob_of_mem (hK.memSobolev (SobolevSpace.memSobolev_toDistribution _)), sob_toDistribution,
      ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (by norm_num)] at h
    have h' := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h
    rw [norm_sub_rev] at h'
    simpa using h'
  obtain ⟨v, hv⟩ : ∃ v, f v = v := ⟨_, hf.fixedPoint_isFixedPt (f := f)⟩
  refine ⟨SobolevSpace.toDistribution v, SobolevSpace.memSobolev_toDistribution v, ?_⟩
  have := congrArg SobolevSpace.toDistribution hv
  simp only [f, SobolevSpace.toDistribution_mk] at this
  exact eq_sub_iff_add_eq.1 this.symm

theorem eq_zero_of_add_eq_zero {K : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ)} {s : ℝ} (hK : OpBound K s s (1 / 2))
    {v : 𝓢'(E, ℂ)} (hv : MemSobolev s 2 v) (h : v + K v = 0) : v = 0 := by
  have e : v = -K v := eq_neg_of_add_eq_zero_left h
  have h1 : sob s v ≤ ENNReal.ofReal (1 / 2) * sob s v := by
    calc sob s v = sob s (-K v) := by rw [← e]
      _ = sob s (K v) := sob_neg _
      _ ≤ _ := hK v hv
  rw [sob_of_mem hv, ← ofReal_norm, ← ENNReal.ofReal_mul (by norm_num)] at h1
  have h2 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h1
  have hx : ‖(SobolevSpace.mk v hv : SobolevSpace E ℂ s)‖ = 0 := by
    linarith [norm_nonneg (SobolevSpace.mk v hv : SobolevSpace E ℂ s)]
  have := congrArg SobolevSpace.toDistribution (norm_eq_zero.1 hx)
  simpa using this

theorem fourierMultiplierCLM_one_sub {r : E → ℂ} (hr : r.HasTemperateGrowth) :
    fourierMultiplierCLM ℂ (fun ξ ↦ 1 - r ξ) =
      ContinuousLinearMap.id ℂ 𝓢'(E, ℂ) - fourierMultiplierCLM ℂ r := by
  ext1 u
  rw [show (fun ξ ↦ 1 - r ξ) = (fun _ ↦ (1 : ℂ)) - r from rfl, fourierMultiplierCLM_apply,
    smulLeftCLM_sub (Function.HasTemperateGrowth.const 1) hr, sub_apply, smulLeftCLM_const,
    one_smul]
  have e : ∀ x y : 𝓢'(E, ℂ), 𝓕⁻ (x - y) = 𝓕⁻ x - 𝓕⁻ y := fun x y ↦ by
    rw [sub_eq_add_neg, FourierTransform.fourierInv_add, FourierTransform.fourierInv_neg,
      ← sub_eq_add_neg]
  rw [e, FourierTransform.fourierInv_fourier_eq, sub_apply, fourierMultiplierCLM_apply]
  rfl

section Q

variable {m n : ℕ} (a : Fin n → 𝓢(E, ℂ)) (w : Fin n → Fin m → E) (x₀ : E)

def Qop (μ : ℝ) (k : ℕ) : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ) :=
  fourierMultiplierCLM ℂ (qNSymb (fun i ↦ a i x₀) w μ k)

def Rop (μ : ℝ) (k : ℕ) : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ) :=
  fourierMultiplierCLM ℂ (rNSymb (fun i ↦ a i x₀) w μ k)

theorem parametrix_comp_frozenOperator {μ : ℝ} (hμ : 0 ≤ μ) (k : ℕ) :
    Qop a w x₀ μ k ∘L P0 a w x₀ = ContinuousLinearMap.id ℂ 𝓢'(E, ℂ) - Rop a w x₀ μ k := by
  rw [Qop, P0, constOp_eq_symb0, fourierMultiplierCLM_compL_fourierMultiplierCLM
    (parametrixSymbol_hasTemperateGrowth _ w) (qNSymb_hasTemperateGrowth _ w μ k), Rop,
    ← fourierMultiplierCLM_one_sub (rNSymb_hasTemperateGrowth _ w μ k)]
  congr 1; ext ξ
  exact parametrixSymbol_mul_inverseSymbolOfOrder _ w hμ k ξ

theorem frozenOperator_comp_parametrix {μ : ℝ} (hμ : 0 ≤ μ) (k : ℕ) :
    P0 a w x₀ ∘L Qop a w x₀ μ k = ContinuousLinearMap.id ℂ 𝓢'(E, ℂ) - Rop a w x₀ μ k := by
  rw [Qop, P0, constOp_eq_symb0, fourierMultiplierCLM_compL_fourierMultiplierCLM
    (qNSymb_hasTemperateGrowth _ w μ k) (parametrixSymbol_hasTemperateGrowth _ w), Rop,
    ← fourierMultiplierCLM_one_sub (rNSymb_hasTemperateGrowth _ w μ k)]
  congr 1; ext ξ
  rw [Pi.mul_apply, mul_comm]
  exact parametrixSymbol_mul_inverseSymbolOfOrder _ w hμ k ξ

variable {cl Cu : ℝ} (hcl : 0 < cl) (hCu : 0 ≤ Cu)
  (hlow : ∀ ξ, cl * ‖ξ‖ ^ m ≤ ‖symb0 (fun i ↦ a i x₀) w ξ‖)
  (hup : ∀ ξ, ‖symb0 (fun i ↦ a i x₀) w ξ‖ ≤ Cu * ‖ξ‖ ^ m)
include hcl hCu hlow hup

theorem opBound_Qop {μ : ℝ} (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) (k : ℕ) (s : ℝ) :
    OpBound (Qop a w x₀ μ k) (s - m) s (k * (2 ^ m * (cl⁻¹ + Cu))) :=
  opBound_fourierMultiplier (qNSymb_hasTemperateGrowth _ w μ k) fun ξ ↦ by
    rw [show (s - m - s) / 2 = -(m : ℝ) / 2 by ring]
    exact qNSymb_bound _ w hcl hCu hlow hup hμ0 hμ1 k ξ

theorem opBound_Qop_small (hm : 1 ≤ m) {μ ε : ℝ} (hμ0 : 0 ≤ μ)
    (hsmall : ∀ ξ : E, ‖qSymb (fun i ↦ a i x₀) w μ ξ‖ * Real.sqrt (1 + ‖ξ‖ ^ 2) ^ (m - 1) ≤ ε)
    (k : ℕ) (s : ℝ) : OpBound (Qop a w x₀ μ k) (s - m + 1) s (k * ε) :=
  opBound_fourierMultiplier (qNSymb_hasTemperateGrowth _ w μ k) fun ξ ↦ by
    have h := norm_le_of_mul_sqrt_pow_le hsmall ξ
    rw [show (s - m + 1 - s) / 2 = -((m - 1 : ℕ) : ℝ) / 2 by push_cast [hm]; ring]
    calc ‖qNSymb _ w μ k ξ‖ ≤ k * ‖qSymb (fun i ↦ a i x₀) w μ ξ‖ := norm_qNSymb_le _ w hμ0 k ξ
      _ ≤ k * (ε * (1 + ‖ξ‖ ^ 2) ^ (-((m - 1 : ℕ) : ℝ) / 2)) := by gcongr
      _ = _ := by ring

theorem opBound_Rop {μ : ℝ} (hμ : 0 < μ) (k : ℕ) (s : ℝ) :
    OpBound (Rop a w x₀ μ k) s (s + (2 * m * k : ℕ)) ((4 ^ m * (1 + (μ * cl ^ 2)⁻¹)) ^ k) :=
  opBound_fourierMultiplier (rNSymb_hasTemperateGrowth _ w μ k) fun ξ ↦ by
    rw [show (s - (s + ((2 * m * k : ℕ) : ℝ))) / 2 = -((2 * m * k : ℕ) : ℝ) / 2 by ring]
    exact rNSymb_bound _ w hcl hCu hlow hup hμ k ξ

end Q

section Small

variable {m n : ℕ} (a : Fin n → 𝓢(E, ℂ)) (w : Fin n → Fin m → E) (N : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ))
  (x₀ : E)

theorem exists_coeff_small {η : ℝ} (hη : 0 < η) :
    ∃ δ, 0 < δ ∧ ∀ i, ∀ y ∈ Metric.closedBall x₀ (2 * δ), ‖a i y - a i x₀‖ ≤ η := by
  have hev : ∀ᶠ y in nhds x₀, ∀ i, a i y ∈ Metric.ball (a i x₀) η :=
    Filter.eventually_all.2 fun i ↦
      (a i).continuous.continuousAt.eventually_mem (Metric.ball_mem_nhds _ hη)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  refine ⟨ε / 4, by positivity, fun i y hy ↦ ?_⟩
  have hy' : y ∈ Metric.ball x₀ ε := by
    rw [Metric.mem_closedBall] at hy; rw [Metric.mem_ball]; linarith
  have := hball y hy' i
  rw [Metric.mem_ball, dist_eq_norm] at this
  exact this.le

theorem opBound_Q_locM {δ : ℝ} (hδ : 0 < δ) (Q : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ)) (s : ℝ)
    {η CQ κ : ℝ} (hη : 0 ≤ η) (hCQ : 0 ≤ CQ) (hκ : 0 ≤ κ)
    (hg : ∀ i x, ‖locCoeff a x₀ hδ i x‖ ≤ η)
    (hQ : OpBound Q (s - m) s CQ) (hQs : OpBound Q (s - m + 1) s κ)
    {Cr : Fin n → ℝ} (hCr0 : ∀ i, 0 ≤ Cr i)
    (hCr : ∀ i, OpBound (mulRem (locCoeff a x₀ hδ i) (s - m)) (s - m) (s - m + 1) (Cr i))
    {CN : ℝ} (hCN0 : 0 ≤ CN) (hCN : OpBound N s (s - m + 1) CN) :
    OpBound (Q ∘L locM a w N x₀ hδ) s s
      (CQ * (η * ∑ i, ∏ j, (2 * Real.pi * ‖w i j‖)) +
        κ * (∑ i, Cr i * ∏ j, (2 * Real.pi * ‖w i j‖) + mulConst (s - m + 1) (bump x₀ hδ) * CN)) := by
  have hP : ∀ i, 0 ≤ ∏ j, (2 * Real.pi * ‖w i j‖) := fun i ↦
    Finset.prod_nonneg fun j _ ↦ by positivity
  have e : Q ∘L locM a w N x₀ hδ =
      ∑ i, (Q ∘L (mulPrin (locCoeff a x₀ hδ i) (s - m) ∘L iteratedLineDerivOpCLM ℂ 𝓢'(E, ℂ) (w i)) +
        Q ∘L (mulRem (locCoeff a x₀ hδ i) (s - m) ∘L iteratedLineDerivOpCLM ℂ 𝓢'(E, ℂ) (w i))) +
      Q ∘L (smulLeftCLM ℂ (bump x₀ hδ : E → ℂ) ∘L N) := by
    ext1 u
    simp only [locM, prinOp, ContinuousLinearMap.comp_apply, add_apply, sum_apply, map_add, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [smulLeftCLM_eq_mulPrin_add_mulRem _ (s - m), map_add]
  rw [e]
  have hterm : ∀ i ∈ Finset.univ, OpBound
      (Q ∘L (mulPrin (locCoeff a x₀ hδ i) (s - m) ∘L iteratedLineDerivOpCLM ℂ 𝓢'(E, ℂ) (w i)) +
        Q ∘L (mulRem (locCoeff a x₀ hδ i) (s - m) ∘L iteratedLineDerivOpCLM ℂ 𝓢'(E, ℂ) (w i))) s s
      (CQ * (η * ∏ j, (2 * Real.pi * ‖w i j‖)) + κ * (Cr i * ∏ j, (2 * Real.pi * ‖w i j‖))) := by
    intro i _
    have h1 := hQ.comp ((opBound_mulPrin _ hη (hg i) (s - m)).comp
      (opBound_iteratedLineDeriv (w i) s) hη) hCQ
    have h2 := hQs.comp ((hCr i).comp (opBound_iteratedLineDeriv (w i) s) (hCr0 i)) hκ
    exact h1.add h2 (by have := hP i; positivity) (by have := hP i; have := hCr0 i; positivity)
  have hsum := OpBound.sum Finset.univ (fun i _ ↦ by have := hP i; have := hCr0 i; positivity) hterm
  have h3 := hQs.comp ((opBound_smulLeft (bump x₀ hδ) (s - m + 1)).comp hCN
    (mulConst_nonneg _ _)) hκ
  refine (hsum.add h3 (Finset.sum_nonneg fun i _ ↦ by have := hP i; have := hCr0 i; positivity)
    (by have := mulConst_nonneg (s - m + 1) (bump x₀ hδ); positivity)).mono (le_of_eq ?_)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  ring

theorem opBound_locM_Q {δ : ℝ} (hδ : 0 < δ) (Q : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ)) (s : ℝ)
    {η CQ κ : ℝ} (hη : 0 ≤ η) (hCQ : 0 ≤ CQ) (hκ : 0 ≤ κ)
    (hg : ∀ i x, ‖locCoeff a x₀ hδ i x‖ ≤ η)
    (hQ : OpBound Q s (s + m) CQ) (hQs : OpBound Q s (s + m - 1) κ)
    {Cr : Fin n → ℝ} (hCr0 : ∀ i, 0 ≤ Cr i)
    (hCr : ∀ i, OpBound (mulRem (locCoeff a x₀ hδ i) s) (s - 1) s (Cr i))
    {CN : ℝ} (hCN0 : 0 ≤ CN) (hCN : OpBound N (s + m - 1) s CN) :
    OpBound (locM a w N x₀ hδ ∘L Q) s s
      (CQ * (η * ∑ i, ∏ j, (2 * Real.pi * ‖w i j‖)) +
        κ * (∑ i, Cr i * ∏ j, (2 * Real.pi * ‖w i j‖) + mulConst s (bump x₀ hδ) * CN)) := by
  have hP : ∀ i, 0 ≤ ∏ j, (2 * Real.pi * ‖w i j‖) := fun i ↦
    Finset.prod_nonneg fun j _ ↦ by positivity
  have e : locM a w N x₀ hδ ∘L Q =
      ∑ i, (mulPrin (locCoeff a x₀ hδ i) s ∘L (iteratedLineDerivOpCLM ℂ 𝓢'(E, ℂ) (w i) ∘L Q) +
        mulRem (locCoeff a x₀ hδ i) s ∘L (iteratedLineDerivOpCLM ℂ 𝓢'(E, ℂ) (w i) ∘L Q)) +
      smulLeftCLM ℂ (bump x₀ hδ : E → ℂ) ∘L (N ∘L Q) := by
    ext1 u
    simp only [locM, prinOp, ContinuousLinearMap.comp_apply, add_apply, sum_apply]
    congr 1
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [smulLeftCLM_eq_mulPrin_add_mulRem _ s]
  rw [e]
  have hterm : ∀ i ∈ Finset.univ, OpBound
      (mulPrin (locCoeff a x₀ hδ i) s ∘L (iteratedLineDerivOpCLM ℂ 𝓢'(E, ℂ) (w i) ∘L Q) +
        mulRem (locCoeff a x₀ hδ i) s ∘L (iteratedLineDerivOpCLM ℂ 𝓢'(E, ℂ) (w i) ∘L Q)) s s
      (η * ((∏ j, (2 * Real.pi * ‖w i j‖)) * CQ) + Cr i * ((∏ j, (2 * Real.pi * ‖w i j‖)) * κ)) := by
    intro i _
    have h1 := (opBound_mulPrin _ hη (hg i) s).comp
      (((opBound_iteratedLineDeriv (w i) (s + m)).congr_idx rfl (by ring)).comp hQ (hP i)) hη
    have h2 := (hCr i).comp
      (((opBound_iteratedLineDeriv (w i) (s + m - 1)).congr_idx rfl (by ring)).comp hQs (hP i))
      (hCr0 i)
    exact h1.add h2 (by have := hP i; positivity) (by have := hP i; have := hCr0 i; positivity)
  have hsum := OpBound.sum Finset.univ (fun i _ ↦ by have := hP i; have := hCr0 i; positivity) hterm
  have h3 := (opBound_smulLeft (bump x₀ hδ) s).comp (hCN.comp hQs hCN0) (mulConst_nonneg _ _)
  refine (hsum.add h3 (Finset.sum_nonneg fun i _ ↦ by have := hP i; have := hCr0 i; positivity)
    (by have := mulConst_nonneg s (bump x₀ hδ); positivity)).mono (le_of_eq ?_)
  rw [Finset.sum_add_distrib]
  have e1 : ∑ i, η * ((∏ j, (2 * Real.pi * ‖w i j‖)) * CQ) =
      CQ * (η * ∑ i, ∏ j, (2 * Real.pi * ‖w i j‖)) := by
    rw [Finset.mul_sum, Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ ↦ by ring
  have e2 : ∑ i, Cr i * ((∏ j, (2 * Real.pi * ‖w i j‖)) * κ) =
      κ * ∑ i, Cr i * ∏ j, (2 * Real.pi * ‖w i j‖) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ ↦ by ring
  rw [e1, e2]; ring

end Small

section Exists

variable {m n : ℕ} (a : Fin n → 𝓢(E, ℂ)) (w : Fin n → Fin m → E) (N : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ))
  (x₀ : E) {cl Cu : ℝ} (hcl : 0 < cl) (hCu : 0 ≤ Cu)
  (hlow : ∀ ξ, cl * ‖ξ‖ ^ m ≤ ‖symb0 (fun i ↦ a i x₀) w ξ‖)
  (hup : ∀ ξ, ‖symb0 (fun i ↦ a i x₀) w ξ‖ ≤ Cu * ‖ξ‖ ^ m)
include hcl hCu hlow hup

theorem exists_small (hm : 1 ≤ m) (hN : HasOrder N ((m : ℝ) - 1)) (k : ℕ) :
    ∃ δ, ∃ hδ : 0 < δ, ∀ S : Finset ℝ, ∃ μ, 0 < μ ∧ μ ≤ 1 ∧ ∀ s ∈ S,
      OpBound (Qop a w x₀ μ k ∘L locM a w N x₀ hδ) s s (1 / 2) ∧
      OpBound (locM a w N x₀ hδ ∘L Qop a w x₀ μ k) s s (1 / 2) := by
  have hP : ∀ i, 0 ≤ ∏ j, (2 * Real.pi * ‖w i j‖) := fun i ↦
    Finset.prod_nonneg fun j _ ↦ by positivity
  obtain ⟨CQ, hCQ0, hCQ_def⟩ : ∃ CQ : ℝ, 0 ≤ CQ ∧ CQ = k * (2 ^ m * (cl⁻¹ + Cu)) :=
    ⟨_, by positivity, rfl⟩
  obtain ⟨SP, hSP0, hSP_def⟩ : ∃ SP : ℝ, 0 ≤ SP ∧ SP = ∑ i, ∏ j, (2 * Real.pi * ‖w i j‖) :=
    ⟨_, Finset.sum_nonneg fun i _ ↦ hP i, rfl⟩
  obtain ⟨η, hη, hη_def⟩ : ∃ η : ℝ, 0 < η ∧ η = 1 / (4 * (CQ * SP + 1)) :=
    ⟨_, by positivity, rfl⟩
  obtain ⟨δ, hδ, hsmall⟩ := exists_coeff_small a x₀ hη
  refine ⟨δ, hδ, fun S ↦ ?_⟩
  have hg : ∀ i x, ‖locCoeff a x₀ hδ i x‖ ≤ η := fun i ↦
    norm_locCoeff_le a x₀ hδ i hη.le (hsmall i)
  have hrem : ∀ (i : Fin n) (r t : ℝ), ∃ C, 0 ≤ C ∧
      OpBound (mulRem (locCoeff a x₀ hδ i) r) t (t + 1) C := by
    intro i r t
    obtain ⟨C, hC0, hC⟩ := hasOrder_mulRem (locCoeff a x₀ hδ i) r t
    exact ⟨C, hC0, fun u hu ↦ by simpa using hC u hu⟩
  choose Cr hCr0 hCr using hrem
  have hNb : ∀ r : ℝ, ∃ C, 0 ≤ C ∧ OpBound N r (r - m + 1) C := by
    intro r
    obtain ⟨C, hC0, hC⟩ := hN r
    exact ⟨C, hC0, fun u hu ↦ by
      have := hC u hu; rwa [show r - ((m : ℝ) - 1) = r - m + 1 by ring] at this⟩
  choose CN hCN0 hCN using hNb
  obtain ⟨X, hX0, hX_def⟩ : ∃ X : ℝ → ℝ, (∀ s, 0 ≤ X s) ∧ X = fun s ↦
      (∑ i, Cr i (s - m) (s - m) * ∏ j, (2 * Real.pi * ‖w i j‖) +
        mulConst (s - m + 1) (bump x₀ hδ) * CN s) +
      (∑ i, Cr i s (s - 1) * ∏ j, (2 * Real.pi * ‖w i j‖) +
        mulConst s (bump x₀ hδ) * CN (s + m - 1)) := by
    refine ⟨_, fun s ↦ ?_, rfl⟩
    have h1 := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) ↦ mul_nonneg (hCr0 i (s - m) (s - m)) (hP i)
    have h2 := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) ↦ mul_nonneg (hCr0 i s (s - 1)) (hP i)
    have := mulConst_nonneg (s - m + 1) (bump x₀ hδ); have := mulConst_nonneg s (bump x₀ hδ)
    have := hCN0 s; have := hCN0 (s + m - 1)
    positivity
  have hSum : 0 ≤ ∑ s ∈ S, X s := Finset.sum_nonneg fun s _ ↦ hX0 s
  obtain ⟨ε, hε, hε_def⟩ : ∃ ε : ℝ, 0 < ε ∧ ε = 1 / (4 * (k + 1) * (∑ s ∈ S, X s + 1)) :=
    ⟨_, by positivity, rfl⟩
  obtain ⟨μ, hμ0, hμ1, hq⟩ := exists_qSymb_small _ w hcl hCu hlow hup hm hε
  refine ⟨μ, hμ0, hμ1, fun s hs ↦ ?_⟩
  have hXs : X s ≤ ∑ s ∈ S, X s := Finset.single_le_sum (fun s _ ↦ hX0 s) hs
  have hkε : (k : ℝ) * ε * X s ≤ 1 / 4 := by
    have h1 : (k : ℝ) * X s ≤ (k + 1) * (∑ s ∈ S, X s + 1) := by
      have := hX0 s
      nlinarith
    have hpos : 0 < 4 * (k + 1) * (∑ s ∈ S, X s + 1) := by positivity
    rw [hε_def, show (k : ℝ) * (1 / (4 * (k + 1) * (∑ s ∈ S, X s + 1))) * X s =
      (k * X s) / (4 * (k + 1) * (∑ s ∈ S, X s + 1)) by ring, div_le_iff₀ hpos]
    nlinarith
  have hηSP : CQ * (η * SP) ≤ 1 / 4 := by
    rw [hη_def, show CQ * (1 / (4 * (CQ * SP + 1)) * SP) = (CQ * SP) / (4 * (CQ * SP + 1)) by ring,
      div_le_iff₀ (by positivity)]
    nlinarith
  have hQ : ∀ t, OpBound (Qop a w x₀ μ k) (t - m) t CQ := fun t ↦ by
    rw [hCQ_def]; exact opBound_Qop a w x₀ hcl hCu hlow hup hμ0.le hμ1 k t
  have hQs : ∀ t, OpBound (Qop a w x₀ μ k) (t - m + 1) t (k * ε) :=
    opBound_Qop_small a w x₀ hcl hCu hlow hup hm hμ0.le hq k
  have hkε0 : 0 ≤ (k : ℝ) * ε := by positivity
  have hXs_def := congrFun hX_def s
  constructor
  · refine (opBound_Q_locM a w N x₀ hδ _ s hη.le hCQ0 hkε0 hg (hQ s) (hQs s)
      (fun i ↦ hCr0 i (s - m) (s - m)) (fun i ↦ (hCr i (s - m) (s - m)).congr_idx rfl (by ring))
      (hCN0 s) (hCN s)).mono ?_
    rw [← hSP_def]
    have : ∑ i, Cr i (s - m) (s - m) * ∏ j, (2 * Real.pi * ‖w i j‖) +
        mulConst (s - m + 1) (bump x₀ hδ) * CN s ≤ X s := by
      have h2 := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) ↦ mul_nonneg (hCr0 i s (s - 1)) (hP i)
      have := mulConst_nonneg s (bump x₀ hδ); have := hCN0 (s + m - 1)
      rw [hXs_def]; nlinarith
    nlinarith
  · refine (opBound_locM_Q a w N x₀ hδ _ s hη.le hCQ0 hkε0 hg ((hQ (s + m)).congr_idx (by ring) rfl)
      ((hQs (s + m - 1)).congr_idx (by ring) rfl) (fun i ↦ hCr0 i s (s - 1))
      (fun i ↦ (hCr i s (s - 1)).congr_idx rfl (by ring))
      (hCN0 (s + m - 1)) ((hCN (s + m - 1)).congr_idx rfl (by ring))).mono ?_
    rw [← hSP_def]
    have : ∑ i, Cr i s (s - 1) * ∏ j, (2 * Real.pi * ‖w i j‖) +
        mulConst s (bump x₀ hδ) * CN (s + m - 1) ≤ X s := by
      have h1 := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) ↦ mul_nonneg (hCr0 i (s - m) (s - m)) (hP i)
      have := mulConst_nonneg (s - m + 1) (bump x₀ hδ); have := hCN0 s
      rw [hXs_def]; nlinarith
    nlinarith

end Exists

end

end GroundTheory.Automorphic.Sobolev
