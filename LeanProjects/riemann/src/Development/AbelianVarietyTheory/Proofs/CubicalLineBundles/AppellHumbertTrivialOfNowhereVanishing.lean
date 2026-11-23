import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory
namespace AppellHumbertTrivial

theorem _root_.GlobalTheory.AppellHumbertTrivial.eq_zero_of_gaussian_decay (f : ℂ → ℂ) (hf : Differentiable ℂ f) (C a : ℝ) (ha : a < 0)
    (h : ∀ t, ‖f t‖ ≤ C * Real.exp (‖t‖ ^ 2 * a)) : f 0 = 0 := by
  have hbd : Bornology.IsBounded (Set.range f) := by
    rw [isBounded_iff_forall_norm_le]
    refine ⟨max C 0, ?_⟩
    rintro _ ⟨t, rfl⟩
    have he : Real.exp (‖t‖ ^ 2 * a) ≤ 1 :=
      Real.exp_le_one_iff.2 (mul_nonpos_of_nonneg_of_nonpos (by positivity) ha.le)
    have hp := Real.exp_pos (‖t‖ ^ 2 * a)
    refine (h t).trans ?_
    rcases le_or_gt 0 C with hC | hC
    · exact (mul_le_of_le_one_right hC he).trans (le_max_left _ _)
    · nlinarith [le_max_right C 0]
  have hconst : ∀ t, f 0 = f t := fun t => hf.apply_eq_apply_of_bounded hbd 0 t
  have h1 : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ 2 * a) Filter.atTop Filter.atBot :=
    ((Filter.tendsto_pow_atTop two_ne_zero).comp tendsto_natCast_atTop_atTop).atTop_mul_const_of_neg ha
  have hlim : Filter.Tendsto (fun n : ℕ => C * Real.exp ((n : ℝ) ^ 2 * a)) Filter.atTop
      (nhds 0) := by
    simpa using (Real.tendsto_exp_atBot.comp h1).const_mul C
  have hle : ∀ n : ℕ, ‖f 0‖ ≤ C * Real.exp ((n : ℝ) ^ 2 * a) := fun n => by
    rw [hconst (n : ℂ)]
    simpa using h (n : ℂ)
  exact norm_le_zero_iff.1 (ge_of_tendsto' hlim hle)

theorem _root_.GlobalTheory.AppellHumbertTrivial.exists_bound_of_periodic {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ]
    (hΛ : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤) {F : Type} [NormedAddCommGroup F]
    (φ : (Fin g → ℂ) → F) (hφ : Continuous φ)
    (hp : ∀ (l : Λ) z, φ (z + l) = φ z) : Bornology.IsBounded (Set.range φ) := by
  haveI : IsZLattice ℝ Λ := ⟨hΛ⟩
  exact (IsZLattice.isCompact_range_of_periodic Λ φ hφ
    (fun z w hw => hp ⟨w, hw⟩ z)).isBounded

variable {g : ℕ}

variable {g : ℕ} in
theorem _root_.GlobalTheory.AppellHumbertTrivial.hermForm_add_left (B : Matrix (Fin g) (Fin g) ℂ) (x y w : Fin g → ℂ) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B (x + y) w = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B x w + _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B y w := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm
  rw [add_dotProduct]

variable {g : ℕ} in
theorem _root_.GlobalTheory.AppellHumbertTrivial.hermForm_add_right (B : Matrix (Fin g) (Fin g) ℂ) (x y w : Fin g → ℂ) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B w (x + y) = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B w x + _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B w y := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm
  rw [star_add, Matrix.mulVec_add, dotProduct_add]

variable {g : ℕ} in
theorem _root_.GlobalTheory.AppellHumbertTrivial.hermForm_smul_left (B : Matrix (Fin g) (Fin g) ℂ) (t : ℂ) (x w : Fin g → ℂ) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B (t • x) w = t * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B x w := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm
  rw [smul_dotProduct, smul_eq_mul]

variable {g : ℕ} in
theorem _root_.GlobalTheory.AppellHumbertTrivial.hermForm_smul_right (B : Matrix (Fin g) (Fin g) ℂ) (t : ℂ) (x w : Fin g → ℂ) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B w (t • x) = star t * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B w x := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm
  rw [star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

variable {g : ℕ} in
theorem _root_.GlobalTheory.AppellHumbertTrivial.hermForm_swap {B : Matrix (Fin g) (Fin g) ℂ} (hB : B.IsHermitian) (x w : Fin g → ℂ) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B w x = star (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B x w) := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm
  simp only [dotProduct, Matrix.mulVec, star_sum, star_mul', Finset.mul_sum, Pi.star_apply,
    star_star]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← hB.apply j i]
  ring

variable {g : ℕ} in
theorem _root_.GlobalTheory.AppellHumbertTrivial.continuous_hermForm_self (B : Matrix (Fin g) (Fin g) ℂ) :
    Continuous fun z => _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B z z := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm
  fun_prop

variable {g : ℕ} in
theorem _root_.GlobalTheory.AppellHumbertTrivial.re_hermForm_add_self {B : Matrix (Fin g) (Fin g) ℂ} (hB : B.IsHermitian)
    (x y : Fin g → ℂ) :
    (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B (x + y) (x + y)).re
      = (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B x x).re + 2 * (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B x y).re + (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B y y).re := by
  rw [_root_.GlobalTheory.AppellHumbertTrivial.hermForm_add_left, _root_.GlobalTheory.AppellHumbertTrivial.hermForm_add_right, _root_.GlobalTheory.AppellHumbertTrivial.hermForm_add_right,
    _root_.GlobalTheory.AppellHumbertTrivial.hermForm_swap hB y x]
  simp only [Complex.add_re, Complex.star_def, Complex.conj_re]
  ring

end AppellHumbertTrivial

variable {g : ℕ} in

theorem _root_.GlobalTheory.appellHumbert_trivial_of_nowhere_vanishing :
    ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ], Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ →
  ∀ (B : Matrix (Fin g) (Fin g) ℂ) (c : Λ → ℂ) (r : (Fin g → ℂ) → ℂ), B.IsHermitian → (∀ l, ‖c l‖ = 1) →
  Differentiable ℂ r → (∀ z, r z ≠ 0) →
  (∀ (l : Λ) z, r (z + l) = c l * Complex.exp (Real.pi * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B z l + Real.pi / 2 * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B l l) * r z) →
  B = 0 ∧ (∀ l, c l = 1) ∧ ∀ z, r z = r 0 := by
  intro g Λ _ hΛ B c r hB hc hr hr0 hper
  have hnorm : ∀ (l : Λ) z, ‖r (z + l)‖ = Real.exp (Real.pi * (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B z l).re +
      Real.pi / 2 * (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B l l).re) * ‖r z‖ := by
    intro l z
    rw [hper l z, norm_mul, norm_mul, hc, one_mul, Complex.norm_exp]
    congr 2
    simp
  have hφper : ∀ (l : Λ) z, ‖r (z + l)‖ * Real.exp (-(Real.pi / 2) * (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B (z + l) (z + l)).re)
      = ‖r z‖ * Real.exp (-(Real.pi / 2) * (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B z z).re) := by
    intro l z
    rw [hnorm, _root_.GlobalTheory.AppellHumbertTrivial.re_hermForm_add_self hB, mul_comm (Real.exp _) ‖r z‖, mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have hφcont : Continuous fun z => ‖r z‖ * Real.exp (-(Real.pi / 2) * (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B z z).re) :=
    hr.continuous.norm.mul (Real.continuous_exp.comp
      (continuous_const.mul (Complex.continuous_re.comp (_root_.GlobalTheory.AppellHumbertTrivial.continuous_hermForm_self B))))
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.1
    (_root_.GlobalTheory.AppellHumbertTrivial.exists_bound_of_periodic Λ hΛ _ hφcont hφper)
  have hup : ∀ z, ‖r z‖ ≤ M * Real.exp (Real.pi / 2 * (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B z z).re) := by
    intro z
    have h := hM _ ⟨z, rfl⟩
    rw [Real.norm_of_nonneg (by positivity)] at h
    calc ‖r z‖ = (‖r z‖ * Real.exp (-(Real.pi / 2) * (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B z z).re)) *
          Real.exp (Real.pi / 2 * (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B z z).re) := by
          rw [mul_assoc, ← Real.exp_add]; simp
      _ ≤ M * Real.exp (Real.pi / 2 * (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B z z).re) :=
          mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
  have hψcont : Continuous fun z => (‖r z‖ * Real.exp (-(Real.pi / 2) * (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B z z).re))⁻¹ :=
    hφcont.inv₀ fun z => (mul_pos (norm_pos_iff.2 (hr0 z)) (Real.exp_pos _)).ne'
  obtain ⟨M', hM'⟩ := isBounded_iff_forall_norm_le.1
    (_root_.GlobalTheory.AppellHumbertTrivial.exists_bound_of_periodic Λ hΛ _ hψcont
      fun l z => congrArg (·⁻¹) (hφper l z))
  have hlow : ∀ z, ‖r z‖⁻¹ ≤ M' * Real.exp (-(Real.pi / 2) * (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B z z).re) := by
    intro z
    have h := hM' _ ⟨z, rfl⟩
    rw [Real.norm_of_nonneg (by positivity)] at h
    calc ‖r z‖⁻¹ = (‖r z‖ * Real.exp (-(Real.pi / 2) * (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B z z).re))⁻¹ *
          Real.exp (-(Real.pi / 2) * (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B z z).re) := by
          rw [mul_inv, mul_assoc, inv_mul_cancel₀ (Real.exp_pos _).ne', mul_one]
      _ ≤ M' * Real.exp (-(Real.pi / 2) * (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B z z).re) :=
          mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
  have hscale : ∀ (t : ℂ) v, (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B (t • v) (t • v)).re = ‖t‖ ^ 2 * (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B v v).re := by
    intro t v
    rw [_root_.GlobalTheory.AppellHumbertTrivial.hermForm_smul_left, _root_.GlobalTheory.AppellHumbertTrivial.hermForm_smul_right, ← mul_assoc]
    have ht : t * star t = ((‖t‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [ht, Complex.re_ofReal_mul]

  have hq0 : ∀ v, (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B v v).re = 0 := by
    intro v
    have hd : Differentiable ℂ fun t : ℂ => r (t • v) := hr.comp (differentiable_id.smul_const v)
    rcases lt_trichotomy (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B v v).re 0 with hneg | hzero | hpos
    · exfalso
      have h := _root_.GlobalTheory.AppellHumbertTrivial.eq_zero_of_gaussian_decay (fun t => r (t • v)) hd M
        (Real.pi / 2 * (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B v v).re) (mul_neg_of_pos_of_neg (by positivity) hneg)
        (fun t => by
          refine (hup (t • v)).trans_eq ?_
          rw [hscale]
          congr 2
          ring)
      exact hr0 0 (by simpa using h)
    · exact hzero
    · exfalso
      have h := _root_.GlobalTheory.AppellHumbertTrivial.eq_zero_of_gaussian_decay (fun t => (r (t • v))⁻¹)
        (hd.inv fun t => hr0 _) M' (-(Real.pi / 2) * (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B v v).re)
        (by nlinarith [Real.pi_pos])
        (fun t => by
          rw [norm_inv]
          refine (hlow (t • v)).trans_eq ?_
          rw [hscale]
          congr 2
          ring)
      exact hr0 0 (by simpa using h)
  have hH : ∀ x y, _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B x y = 0 := by
    intro x y
    have h1 := _root_.GlobalTheory.AppellHumbertTrivial.re_hermForm_add_self hB x y
    have h2 := _root_.GlobalTheory.AppellHumbertTrivial.re_hermForm_add_self hB x (Complex.I • y)
    simp only [hq0] at h1
    rw [hq0, hq0, hq0, _root_.GlobalTheory.AppellHumbertTrivial.hermForm_smul_right] at h2
    refine Complex.ext ?_ ?_
    · simp only [Complex.zero_re]
      linarith
    · simp [Complex.star_def] at h2
      simpa using h2
  have hB0 : B = 0 := by
    ext i j
    have h := hH (Pi.single i 1) (Pi.single j 1)
    unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm at h
    simpa using h
  have hbdd : Bornology.IsBounded (Set.range r) := by
    rw [isBounded_iff_forall_norm_le]
    refine ⟨M, ?_⟩
    rintro _ ⟨z, rfl⟩
    simpa [hq0] using hup z
  have hconst : ∀ z, r z = r 0 := fun z => hr.apply_eq_apply_of_bounded hbdd z 0
  refine ⟨hB0, fun l => ?_, hconst⟩
  have h := hper l 0
  simp only [hH, hconst (0 + (l : Fin g → ℂ)), mul_zero, add_zero, Complex.exp_zero, mul_one] at h
  exact mul_right_cancel₀ (hr0 0) (h.symm.trans (one_mul _).symm)

end GlobalTheory
