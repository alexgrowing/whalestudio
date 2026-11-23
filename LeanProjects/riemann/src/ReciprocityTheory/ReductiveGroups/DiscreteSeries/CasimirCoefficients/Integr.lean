import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IsClosedKset
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.HaarPolar
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PhiDecayCore
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.LholClmEventually
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IntegrA

noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

variable {ε : Fin n → Bool} {lam : Fin n → ℝ}

theorem psiM_integrable (T : KType ε (lowK ε lam)) (μ : Fin n → ℤ) (hμ : IsMu lam μ)
    (hlam : IsHCParam lam) {h : ℝ} (hgap : GapAtLeast ε lam h) (hq : 1 ≤ q0 ε)
    (ν : Measure (UJ ε)) [ν.IsHaarMeasure] :
    (16 * (n : ℝ) * q0 ε < h → Integrable (fun g : UJ ε => PsiM T μ (toM g)) ν) ∧
    (8 * (n : ℝ) * q0 ε < h → MemLp (fun g : UJ ε => PsiM T μ (toM g)) 2 ν) ∧
    (∀ s : ℝ, 0 ≤ s → 8 * (n : ℝ) * q0 ε + 4 * s * Real.sqrt (2 * q0 ε) < h →
      Integrable (fun g : UJ ε => ‖PsiM T μ (toM g)‖ ^ 2 * hs (toM g) ^ (s / 2)) ν) := by
  have hq1 : (1 : ℝ) ≤ q0 ε := by exact_mod_cast hq
  set c : ℝ := Real.sqrt (2 * q0 ε) with hcdef
  have hc1 : 1 ≤ c := Real.one_le_sqrt.mpr (by linarith)
  have hc0 : 0 < c := by linarith
  have hcc : c ^ 2 = 2 * q0 ε := Real.sq_sqrt (by positivity)
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  set f : UJ ε → (T.V →L[ℂ] T.V) := fun g => PsiM T μ (toM g) with hfdef
  have hfc : Continuous f :=
    (psiM_continuousOn T μ hμ).comp_continuous (continuous_toM ε) (fun g => g.2)

  have key : 0 ≤ h → ∀ (k : KG ε) (X : Matrix (Fin n) (Fin n) ℂ), inP ε X →
      ‖f (toUJ ε (toMK k * NormedSpace.exp X))‖ ≤
        Real.exp (h / (32 * c ^ 2)) * Real.exp (-(h / (8 * c)) * Real.sqrt (hs X)) ∧
      hs (toM (toUJ ε (toMK k * NormedSpace.exp X))) ≤ n * Real.exp (2 * Real.sqrt (hs X)) := by
    intro hh k X hX
    have hm : toM (toUJ ε (toMK k * NormedSpace.exp X)) = toMK k * NormedSpace.exp X :=
      toM_toUJ (inUJ_kexp k hX)
    refine ⟨?_, ?_⟩
    · show ‖PsiM T μ (toM (toUJ ε (toMK k * NormedSpace.exp X)))‖ ≤ _
      rw [hm, ← Real.exp_add]
      exact (psiM_dec T μ hμ hlam hgap hq k hX).trans
        (Real.exp_le_exp.2 (min_bound hh hc0 (hs_nonnegVG X)))
    · rw [hm, hs_kmulVG]
      exact hs_exp_leVG X
  refine ⟨fun hth => ?_, fun hth => ?_, fun s hs0 hth => ?_⟩
  ·
    have hh : 0 ≤ h := by
      have : 0 ≤ 16 * (n : ℝ) * q0 ε := by positivity
      linarith
    refine integrable_of_polar hq ν f hfc (M := Real.exp (h / (32 * c ^ 2)))
      (δ := h / (8 * c) - n * c) (Real.exp_pos _).le ?_ ?_
    · rw [sub_pos, lt_div_iff₀ (by positivity)]
      nlinarith
    · intro k X hX
      have e : -(h / (8 * c) - n * c + n * c) * Real.sqrt (hs X) = -(h / (8 * c)) * Real.sqrt (hs X) := by
        ring
      rw [e]
      exact (key hh k X hX).1
  ·
    have hh : 0 ≤ h := by
      have : 0 ≤ 8 * (n : ℝ) * q0 ε := by positivity
      linarith
    refine (memLp_two_iff_integrable_sq_norm hfc.aestronglyMeasurable).mpr ?_
    refine integrable_of_polar hq ν (fun g => ‖f g‖ ^ 2) (hfc.norm.pow 2)
      (M := Real.exp (h / (32 * c ^ 2)) ^ 2) (δ := h / (4 * c) - n * c) (by positivity) ?_ ?_
    · rw [sub_pos, lt_div_iff₀ (by positivity)]
      nlinarith
    · intro k X hX
      have hb := (key hh k X hX).1
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      calc ‖f (toUJ ε (toMK k * NormedSpace.exp X))‖ ^ 2
          ≤ (Real.exp (h / (32 * c ^ 2)) * Real.exp (-(h / (8 * c)) * Real.sqrt (hs X))) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) hb 2
        _ = Real.exp (h / (32 * c ^ 2)) ^ 2 *
              Real.exp (-(h / (4 * c) - n * c + n * c) * Real.sqrt (hs X)) := by
            rw [mul_pow, ← Real.exp_nat_mul (-(h / (8 * c)) * Real.sqrt (hs X)) 2]
            congr 2
            field_simp
            ring
  ·
    have hh : 0 ≤ h := by
      have : 0 ≤ 8 * (n : ℝ) * q0 ε + 4 * s * c := by positivity
      linarith
    have hs2 : 0 ≤ s / 2 := by linarith
    have hcw : Continuous fun g : UJ ε => hs (toM g) ^ (s / 2) :=
      (hs_contVG.comp (continuous_toM ε)).rpow_const (fun _ => Or.inr hs2)
    refine integrable_of_polar hq ν (fun g => ‖f g‖ ^ 2 * hs (toM g) ^ (s / 2))
      ((hfc.norm.pow 2).mul hcw) (M := Real.exp (h / (32 * c ^ 2)) ^ 2 * (n : ℝ) ^ (s / 2))
      (δ := h / (4 * c) - s - n * c) (by positivity) ?_ ?_
    · have e : h / (4 * c) - s - n * c = (h - (8 * n * q0 ε + 4 * s * c)) / (4 * c) := by
        field_simp
        rw [hcc]
        ring
      rw [e]
      exact div_pos (by linarith) (by positivity)
    · intro k X hX
      obtain ⟨hb, hw⟩ := key hh k X hX
      set g := toUJ ε (toMK k * NormedSpace.exp X) with hgdef
      set r := Real.sqrt (hs X) with hrdef
      have hw0 : 0 ≤ hs (toM g) ^ (s / 2) := Real.rpow_nonneg (hs_nonnegVG _) _
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) hw0)]
      have hw' : hs (toM g) ^ (s / 2) ≤ (n : ℝ) ^ (s / 2) * Real.exp (s * r) := by
        calc hs (toM g) ^ (s / 2) ≤ ((n : ℝ) * Real.exp (2 * r)) ^ (s / 2) :=
              Real.rpow_le_rpow (hs_nonnegVG _) hw hs2
          _ = (n : ℝ) ^ (s / 2) * Real.exp (s * r) := by
              rw [Real.mul_rpow hn0 (Real.exp_pos _).le, ← Real.exp_mul]
              congr 2
              ring
      have hf2 : ‖f g‖ ^ 2 ≤ Real.exp (h / (32 * c ^ 2)) ^ 2 * Real.exp (-(h / (4 * c)) * r) := by
        calc ‖f g‖ ^ 2 ≤ (Real.exp (h / (32 * c ^ 2)) * Real.exp (-(h / (8 * c)) * r)) ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) hb 2
          _ = _ := by
              rw [mul_pow, ← Real.exp_nat_mul (-(h / (8 * c)) * r) 2]
              congr 2
              field_simp
              ring
      calc ‖f g‖ ^ 2 * hs (toM g) ^ (s / 2)
          ≤ (Real.exp (h / (32 * c ^ 2)) ^ 2 * Real.exp (-(h / (4 * c)) * r)) *
              ((n : ℝ) ^ (s / 2) * Real.exp (s * r)) :=
            mul_le_mul hf2 hw' hw0 (by positivity)
        _ = Real.exp (h / (32 * c ^ 2)) ^ 2 * (n : ℝ) ^ (s / 2) *
              Real.exp (-(h / (4 * c) - s - n * c + n * c) * r) := by
            rw [show -(h / (4 * c) - s - n * c + n * c) * r = -(h / (4 * c)) * r + s * r by ring,
              Real.exp_add]
            ring

end ReciprocityTheory.ChartRestriction.DS.S7
