import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.IsBand

open MeasureTheory Filter UpperTheory.Lit.Cusp
open scoped Topology

theorem UpperTheory.Lit.Cusp.isEig_of_isBand :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
      [SecondCountableTopology G] (N : Set G) (a : ℝ → G) (H : G → ℝ) (h : G → ℂ),
      IsRay N a H → IsBand N H h → ∀ s : ℝ, ∃ C : ℝ,
        IsEig N a s C (fun g => ∫ t : ℝ, Complex.exp (-((s * t : ℝ) * Complex.I)) * h (g * a t)) ∧
          ∀ g, Integrable (fun t : ℝ => h (g * a t)) ∧ ∫ t : ℝ, ‖h (g * a t)‖ ≤ C := by
  intro G _ _ _ _ _ _ N a H h hr hb s
  obtain ⟨hc, ⟨B, hB⟩, hN, ⟨R, hR⟩⟩ := hb
  have ha := hr.cont
  have hH := hr.contH
  have he1 : ∀ x : ℝ, ‖Complex.exp (-((x : ℂ) * Complex.I))‖ = 1 := fun x => by
    rw [← neg_mul, ← Complex.ofReal_neg, Complex.norm_exp_ofReal_mul_I]
  have hsupp : ∀ g t, h (g * a t) ≠ 0 → |H g + t| ≤ R := fun g t hne => by
    have := hR _ hne
    rwa [hr.move] at this
  have hint : ∀ g, Integrable (fun t : ℝ => h (g * a t)) := by
    intro g
    refine Continuous.integrable_of_hasCompactSupport (by fun_prop) ?_
    refine HasCompactSupport.intro (isCompact_Icc (a := -R - H g) (b := R - H g)) ?_
    intro t ht
    by_contra hne
    apply ht
    have := abs_le.mp (hsupp g t hne)
    constructor <;> linarith [this.1, this.2]
  have hbound : ∀ g, ∫ t : ℝ, ‖h (g * a t)‖ ≤ 2 * |R| * |B| := by
    intro g
    have hle : ∀ t, ‖h (g * a t)‖ ≤ (Set.Icc (-R - H g) (R - H g)).indicator (fun _ => |B|) t := by
      intro t
      by_cases hne : h (g * a t) = 0
      · rw [hne, norm_zero]
        exact Set.indicator_nonneg (fun _ _ => abs_nonneg _) _
      · have := abs_le.mp (hsupp g t hne)
        rw [Set.indicator_of_mem (by constructor <;> linarith [this.1, this.2])]
        exact (hB _).trans (le_abs_self B)
    refine (integral_mono (hint g).norm
      ((continuous_const.integrableOn_Icc).integrable_indicator measurableSet_Icc) hle).trans ?_
    rw [integral_indicator_const _ measurableSet_Icc, smul_eq_mul, Real.volume_real_Icc]
    have h1 : max (R - H g - (-R - H g)) 0 ≤ 2 * |R| :=
      max_le (by linarith [le_abs_self R]) (by positivity)
    exact mul_le_mul_of_nonneg_right h1 (abs_nonneg B)
  have hshift : ∀ g, (∫ t : ℝ, Complex.exp (-((s * t : ℝ) * Complex.I)) * h (g * a t)) =
      Complex.exp (((s * H g : ℝ) : ℂ) * Complex.I) *
        ∫ t : ℝ, Complex.exp (-((s * t : ℝ) * Complex.I)) * h (g * a (t - H g)) := by
    intro g
    rw [← integral_const_mul]
    conv_lhs => rw [← integral_sub_right_eq_self _ (H g)]
    congr 1
    ext t
    rw [← mul_assoc, ← Complex.exp_add]
    congr 1
    congr 1
    push_cast
    ring
  have hΦ : Continuous fun g =>
      ∫ t : ℝ, Complex.exp (-((s * t : ℝ) * Complex.I)) * h (g * a (t - H g)) := by
    refine continuous_of_dominated (bound := (Set.Icc (-R) R).indicator (fun _ => |B|)) ?_ ?_ ?_ ?_
    · intro g
      exact (by fun_prop : Continuous fun t : ℝ =>
        Complex.exp (-((s * t : ℝ) * Complex.I)) * h (g * a (t - H g))).aestronglyMeasurable
    · intro g
      refine Eventually.of_forall fun t => ?_
      rw [norm_mul, he1, one_mul]
      by_cases hne : h (g * a (t - H g)) = 0
      · rw [hne, norm_zero]
        exact Set.indicator_nonneg (fun _ _ => abs_nonneg _) _
      · have := abs_le.mp (hsupp g _ hne)
        rw [Set.indicator_of_mem (by constructor <;> linarith [this.1, this.2])]
        exact (hB _).trans (le_abs_self B)
    · exact (continuous_const.integrableOn_Icc).integrable_indicator measurableSet_Icc
    · exact Eventually.of_forall fun t => by fun_prop
  refine ⟨2 * |R| * |B|, ⟨?_, ?_, ?_, ?_⟩, fun g => ⟨hint g, hbound g⟩⟩
  · rw [show (fun g => ∫ t : ℝ, Complex.exp (-((s * t : ℝ) * Complex.I)) * h (g * a t)) =
        fun g => Complex.exp (((s * H g : ℝ) : ℂ) * Complex.I) *
          ∫ t : ℝ, Complex.exp (-((s * t : ℝ) * Complex.I)) * h (g * a (t - H g)) from funext hshift]
    exact (Complex.continuous_exp.comp (by fun_prop)).mul hΦ
  · intro g
    refine (norm_integral_le_integral_norm _).trans (le_of_eq_of_le ?_ (hbound g))
    congr 1
    ext t
    rw [norm_mul, he1, one_mul]
  · intro g m hm
    beta_reduce
    congr 1
    ext t
    rw [show g * m * a t = g * a t * ((a t)⁻¹ * m * a t) by group, hN _ _ (hr.norm t m hm)]
  · intro g u
    beta_reduce
    rw [← integral_const_mul]
    conv_rhs => rw [← integral_add_left_eq_self _ u]
    congr 1
    ext t
    rw [mul_assoc g, ← hr.add, ← mul_assoc, ← Complex.exp_add]
    congr 1
    congr 1
    push_cast
    ring
