import Mathlib
import Formalism.GL3MeanSquares.PrimeCountAsymptoticInProgressions
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Formalism.CyclotomicNorms.StatementI
import Development.AbelianVarietyTheory.Definitions.Foundations.RayPrimes
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ZeroCount
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DirichletLZerosInWindowFiniteAndPosOrderStatement
open Finset ArithmeticFunction NumberField IsDedekindDomain Filter Topology GlobalTheory.Mem.An Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
open scoped nonZeroDivisors

namespace GlobalTheory.Mem.An

theorem zsumR_eq_sum_toFinset {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (t T : ℝ) (f : ℂ → ℝ)
    (h : (zerosIn χ t T).Finite) :
    zsumR χ t T f = ∑ ρ ∈ h.toFinset, (zmult χ ρ : ℝ) * f ρ := by
  unfold zsumR
  exact finsum_mem_eq_finite_toFinset_sum _ h

open Classical in

theorem sum_indicator_le_zsumR {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (t T : ℝ) (S : Finset ℂ)
    (h : (zerosIn χ t T).Finite) :
    ∑ ρ ∈ S, (zmult χ ρ : ℝ) * (if ρ ∈ zerosIn χ t T then 1 else 0) ≤ zsumR χ t T (fun _ => 1) := by
  rw [zsumR_eq_sum_toFinset χ t T _ h]
  simp only [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro x hx
    rw [Finset.mem_filter] at hx
    exact h.mem_toFinset.mpr hx.2
  · intro x _ _
    exact Nat.cast_nonneg _

open Classical in

theorem recip_le_sum_windows {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ) (ρ : ℂ)
    (hρ : ρ ∈ zerosIn χ 0 T) :
    (if 1 < |ρ.im| then 1 / ‖ρ‖ else 0 : ℝ) ≤
      ∑ k ∈ Icc 1 ⌊T⌋₊, (k : ℝ)⁻¹ * ((if ρ ∈ zerosIn χ (k : ℝ) 1 then 1 else 0) +
        (if ρ ∈ zerosIn χ (-(k : ℝ)) 1 then 1 else 0)) := by
  have hnn : ∀ j : ℕ, (0 : ℝ) ≤ (j : ℝ)⁻¹ * ((if ρ ∈ zerosIn χ (j : ℝ) 1 then 1 else 0) +
      (if ρ ∈ zerosIn χ (-(j : ℝ)) 1 then 1 else 0)) := by
    intro j
    apply mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg j))
    apply add_nonneg <;> split_ifs <;> norm_num
  by_cases h1 : 1 < |ρ.im|
  · rw [if_pos h1]
    obtain ⟨hre0, hre1, hT, hL⟩ := hρ
    rw [sub_zero] at hT
    have hk1 : 1 ≤ ⌊|ρ.im|⌋₊ := Nat.le_floor (by rw [Nat.cast_one]; exact h1.le)
    have hkT : ⌊|ρ.im|⌋₊ ≤ ⌊T⌋₊ := Nat.floor_mono hT
    have hkle : (⌊|ρ.im|⌋₊ : ℝ) ≤ |ρ.im| := Nat.floor_le (abs_nonneg _)
    have hklt : |ρ.im| < ⌊|ρ.im|⌋₊ + 1 := Nat.lt_floor_add_one _
    have hkpos : (0 : ℝ) < ⌊|ρ.im|⌋₊ := by exact_mod_cast hk1
    have hind : (1 : ℝ) ≤ (if ρ ∈ zerosIn χ (⌊|ρ.im|⌋₊ : ℝ) 1 then 1 else 0) +
        (if ρ ∈ zerosIn χ (-(⌊|ρ.im|⌋₊ : ℝ)) 1 then 1 else 0) := by
      rcases le_or_gt 0 ρ.im with him | him
      · have hmem : ρ ∈ zerosIn χ (⌊|ρ.im|⌋₊ : ℝ) 1 := by
          refine ⟨hre0, hre1, ?_, hL⟩
          have hab : |ρ.im| = ρ.im := abs_of_nonneg him
          rw [abs_le]
          constructor <;> linarith
        rw [if_pos hmem]
        split_ifs <;> norm_num
      · have hmem : ρ ∈ zerosIn χ (-(⌊|ρ.im|⌋₊ : ℝ)) 1 := by
          refine ⟨hre0, hre1, ?_, hL⟩
          have hab : |ρ.im| = -ρ.im := abs_of_neg him
          rw [abs_le]
          constructor <;> linarith
        rw [if_pos hmem]
        split_ifs <;> norm_num
    calc 1 / ‖ρ‖ ≤ ((⌊|ρ.im|⌋₊ : ℕ) : ℝ)⁻¹ := by
          rw [one_div]
          exact inv_anti₀ hkpos (hkle.trans (Complex.abs_im_le_norm ρ))
      _ ≤ ((⌊|ρ.im|⌋₊ : ℕ) : ℝ)⁻¹ * ((if ρ ∈ zerosIn χ (⌊|ρ.im|⌋₊ : ℝ) 1 then 1 else 0) +
          (if ρ ∈ zerosIn χ (-(⌊|ρ.im|⌋₊ : ℝ)) 1 then 1 else 0)) :=
          le_mul_of_one_le_right (inv_nonneg.mpr hkpos.le) hind
      _ ≤ _ := Finset.single_le_sum (fun j _ => hnn j) (Finset.mem_Icc.mpr ⟨hk1, hkT⟩)
  · rw [if_neg h1]
    exact Finset.sum_nonneg (fun j _ => hnn j)

theorem zsumR_recip_le : GlobalTheory.Mem.An.ZeroCount → ∃ C : ℝ, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → ∀ T : ℝ, 2 ≤ T → zsumR χ 0 T (fun ρ => if 1 < |ρ.im| then 1 / ‖ρ‖ else 0) ≤ C * Real.log (q * T) ^ 2 ∧ zsumR χ 0 1 (fun _ => 1) ≤ C * Real.log (3 * q) := by
  classical
  rintro ⟨C0, hC0⟩
  set D := max C0 0 with hD
  have hD0 : 0 ≤ D := le_max_right _ _
  have hZ : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → ∀ t : ℝ,
      zsumR χ t 1 (fun _ => 1) ≤ D * Real.log (q * (|t| + 2)) := by
    intro q _ χ hχ t
    refine (hC0 q χ hχ t).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.log_nonneg ?_))
    have : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    nlinarith [abs_nonneg t]
  refine ⟨12 * D, ?_⟩
  intro q _ χ hχ T hT
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  refine ⟨?_, ?_⟩
  · obtain ⟨hfin, _⟩ := GlobalTheory.T.dirichletLZerosInWindow_finite_and_pos_order q χ 0 T
    have hfin' : ∀ t : ℝ, (zerosIn χ t 1).Finite := fun t => (GlobalTheory.T.dirichletLZerosInWindow_finite_and_pos_order q χ t 1).1
    have hN1 : 1 ≤ ⌊T⌋₊ := Nat.le_floor (by rw [Nat.cast_one]; linarith)
    have hNT : (⌊T⌋₊ : ℝ) ≤ T := Nat.floor_le (by linarith)
    have hNpos : (0 : ℝ) < ⌊T⌋₊ := by exact_mod_cast hN1
    rw [zsumR_eq_sum_toFinset χ 0 T _ hfin]
    have hsplit : ∀ k : ℕ, ∑ ρ ∈ hfin.toFinset, (zmult χ ρ : ℝ) * ((k : ℝ)⁻¹ *
        ((if ρ ∈ zerosIn χ (k : ℝ) 1 then 1 else 0) + (if ρ ∈ zerosIn χ (-(k : ℝ)) 1 then 1 else 0))) =
        (k : ℝ)⁻¹ * (∑ ρ ∈ hfin.toFinset, (zmult χ ρ : ℝ) * (if ρ ∈ zerosIn χ (k : ℝ) 1 then 1 else 0) +
          ∑ ρ ∈ hfin.toFinset, (zmult χ ρ : ℝ) * (if ρ ∈ zerosIn χ (-(k : ℝ)) 1 then 1 else 0)) := by
      intro k
      rw [← Finset.sum_add_distrib, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ρ _
      ring
    have hLA : 0 ≤ Real.log (q * (T + 2)) := Real.log_nonneg (by nlinarith)
    calc ∑ ρ ∈ hfin.toFinset, (zmult χ ρ : ℝ) * (if 1 < |ρ.im| then 1 / ‖ρ‖ else 0)
        ≤ ∑ ρ ∈ hfin.toFinset, (zmult χ ρ : ℝ) * ∑ k ∈ Icc 1 ⌊T⌋₊, (k : ℝ)⁻¹ *
            ((if ρ ∈ zerosIn χ (k : ℝ) 1 then 1 else 0) + (if ρ ∈ zerosIn χ (-(k : ℝ)) 1 then 1 else 0)) := by
          apply Finset.sum_le_sum
          intro ρ hρ
          exact mul_le_mul_of_nonneg_left (recip_le_sum_windows χ T ρ (hfin.mem_toFinset.mp hρ))
            (Nat.cast_nonneg _)
      _ = ∑ k ∈ Icc 1 ⌊T⌋₊, ∑ ρ ∈ hfin.toFinset, (zmult χ ρ : ℝ) * ((k : ℝ)⁻¹ *
            ((if ρ ∈ zerosIn χ (k : ℝ) 1 then 1 else 0) + (if ρ ∈ zerosIn χ (-(k : ℝ)) 1 then 1 else 0))) := by
          simp_rw [Finset.mul_sum]
          exact Finset.sum_comm
      _ ≤ ∑ k ∈ Icc 1 ⌊T⌋₊, (k : ℝ)⁻¹ * (2 * D * Real.log (q * (T + 2))) := by
          apply Finset.sum_le_sum
          intro k hk
          have hk' := Finset.mem_Icc.mp hk
          have hkT : (k : ℝ) ≤ T := (Nat.cast_le.mpr hk'.2).trans hNT
          rw [hsplit k]
          apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg k))
          have e1 := (sum_indicator_le_zsumR χ (k : ℝ) 1 hfin.toFinset (hfin' _)).trans (hZ q χ hχ k)
          have e2 := (sum_indicator_le_zsumR χ (-(k : ℝ)) 1 hfin.toFinset (hfin' _)).trans
            (hZ q χ hχ (-(k : ℝ)))
          rw [abs_neg] at e2
          have hlog : Real.log (q * (|(k : ℝ)| + 2)) ≤ Real.log (q * (T + 2)) := by
            apply Real.log_le_log (by nlinarith [abs_nonneg (k : ℝ)])
            rw [abs_of_nonneg (Nat.cast_nonneg k)]
            nlinarith
          have := mul_le_mul_of_nonneg_left hlog hD0
          linarith
      _ = 2 * D * Real.log (q * (T + 2)) * ∑ k ∈ Icc 1 ⌊T⌋₊, (k : ℝ)⁻¹ := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _
          ring
      _ ≤ 2 * D * Real.log (q * (T + 2)) * (1 + Real.log T) := by
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by linarith) hLA)
          have h := harmonic_le_one_add_log ⌊T⌋₊
          simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] at h
          have := Real.log_le_log hNpos hNT
          linarith
      _ ≤ 12 * D * Real.log (q * T) ^ 2 := by
          have hqT : 2 ≤ (q : ℝ) * T := by nlinarith
          have hu : Real.log 2 ≤ Real.log (q * T) := Real.log_le_log (by norm_num) hqT
          have hl2 := Real.log_two_gt_d9
          have hA : Real.log (q * (T + 2)) ≤ 2 * Real.log (q * T) := by
            have h := Real.log_le_log (by nlinarith : (0 : ℝ) < q * (T + 2))
              (by nlinarith : (q : ℝ) * (T + 2) ≤ 2 * (q * T))
            rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt (by nlinarith : (0 : ℝ) < q * T))] at h
            linarith
          have hB : 1 + Real.log T ≤ 3 * Real.log (q * T) := by
            have := Real.log_le_log (by linarith : (0 : ℝ) < T) (by nlinarith : T ≤ (q : ℝ) * T)
            linarith
          have hB0 : 0 ≤ 1 + Real.log T := by
            have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ T)
            linarith
          have h := mul_le_mul hA hB hB0 (by linarith)
          have h' := mul_le_mul_of_nonneg_left h (by linarith : (0 : ℝ) ≤ 2 * D)
          calc 2 * D * Real.log (q * (T + 2)) * (1 + Real.log T)
              = 2 * D * (Real.log (q * (T + 2)) * (1 + Real.log T)) := by ring
            _ ≤ 2 * D * (2 * Real.log (q * T) * (3 * Real.log (q * T))) := h'
            _ = 12 * D * Real.log (q * T) ^ 2 := by ring
  · have h := hZ q χ hχ 0
    rw [abs_zero, zero_add] at h
    refine h.trans ?_
    have h1 : Real.log (q * 2) ≤ Real.log (3 * q) := Real.log_le_log (by linarith) (by linarith)
    have h2 : 0 ≤ Real.log (3 * q) := Real.log_nonneg (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left h1 hD0, mul_nonneg hD0 h2]

end GlobalTheory.Mem.An
