import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.ExistsSplitIdem

noncomputable section

open Filter Topology

namespace Formalism.IndefR.Fin.U1

theorem circle_eq_one_of_re_pos (z : Circle) (h : ∀ n : ℕ, 0 < ((z ^ n : Circle) : ℂ).re) : z = 1 := by
  set θ := Complex.arg (z : ℂ) with hθ
  have hz : (z : ℂ) = Complex.exp (θ * Complex.I) := by
    have := Complex.norm_mul_exp_arg_mul_I (z : ℂ)
    rw [Circle.norm_coe, Complex.ofReal_one, one_mul] at this
    exact this.symm
  have hre : ∀ n : ℕ, ((z ^ n : Circle) : ℂ).re = Real.cos (n * θ) := by
    intro n
    rw [Circle.coe_pow, hz, ← Complex.exp_nat_mul, ← mul_assoc, ← Complex.ofReal_natCast, ← Complex.ofReal_mul,
      Complex.exp_ofReal_mul_I_re]
  by_cases h0 : θ = 0
  · apply Circle.ext
    rw [hz, h0, Complex.ofReal_zero, zero_mul, Complex.exp_zero, Circle.coe_one]
  · exfalso
    set t := |θ| with ht
    have ht0 : 0 < t := abs_pos.mpr h0
    have htpi : t ≤ Real.pi := Complex.abs_arg_le_pi _
    set n := ⌈Real.pi / (2 * t)⌉₊ with hn
    have h1 : Real.pi / 2 ≤ n * t := by
      have := Nat.le_ceil (Real.pi / (2 * t))
      rw [← hn] at this
      have e : Real.pi / 2 = Real.pi / (2 * t) * t := by field_simp
      rw [e]; exact mul_le_mul_of_nonneg_right this ht0.le
    have h2 : (n : ℝ) * t < Real.pi / 2 + t := by
      have := Nat.ceil_lt_add_one (div_nonneg Real.pi_pos.le (by positivity : (0 : ℝ) ≤ 2 * t))
      rw [← hn] at this
      have e : Real.pi / 2 + t = (Real.pi / (2 * t) + 1) * t := by field_simp
      rw [e]; exact mul_lt_mul_of_pos_right this ht0
    have hc : Real.cos (n * θ) = Real.cos (n * t) := by
      rw [← Real.cos_abs (n * θ), abs_mul, Nat.abs_cast]
    have := h n
    rw [hre, hc] at this
    have := Real.cos_nonpos_of_pi_div_two_le_of_le h1 (by linarith)
    linarith

section Defs

variable {K : Type*} [Field K]

def nrm (Δ p r : K) : K := p * p - Δ * (r * r)

def cAq (Δ a b p r : K) : K := (a * (p * p + Δ * (r * r)) - Δ * b * (2 * p * r)) / nrm Δ p r

def cBq (Δ a b p r : K) : K := (b * (p * p + Δ * (r * r)) - a * (2 * p * r)) / nrm Δ p r

end Defs

section Loc

variable {K : Type*} [NormedField K]

theorem loc_of (Δ a b p0 r0 : K) (hN : nrm Δ p0 r0 ≠ 0) (hA : cAq Δ a b p0 r0 = 1) (hB : cBq Δ a b p0 r0 = 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ η > 0, ∀ p r : K, ‖p - p0‖ < η → ‖r - r0‖ < η →
      nrm Δ p r ≠ 0 ∧ ‖cAq Δ a b p r - 1‖ < ε ∧ ‖cBq Δ a b p r‖ < ε := by
  have hcN : Continuous fun y : K × K => nrm Δ y.1 y.2 := by unfold nrm; fun_prop
  have hn1 : Continuous fun y : K × K => a * (y.1 * y.1 + Δ * (y.2 * y.2)) - Δ * b * (2 * y.1 * y.2) := by
    fun_prop
  have hn2 : Continuous fun y : K × K => b * (y.1 * y.1 + Δ * (y.2 * y.2)) - a * (2 * y.1 * y.2) := by
    fun_prop
  have hA' : ContinuousAt (fun y : K × K => cAq Δ a b y.1 y.2) (p0, r0) := by
    unfold cAq; exact hn1.continuousAt.div hcN.continuousAt hN
  have hB' : ContinuousAt (fun y : K × K => cBq Δ a b y.1 y.2) (p0, r0) := by
    unfold cBq; exact hn2.continuousAt.div hcN.continuousAt hN
  have e1 : ∀ᶠ y in 𝓝 ((p0, r0) : K × K), nrm Δ y.1 y.2 ≠ 0 := hcN.continuousAt.eventually_ne hN
  have e2 : ∀ᶠ y in 𝓝 ((p0, r0) : K × K), ‖cAq Δ a b y.1 y.2 - 1‖ < ε := by
    have t := hA'.tendsto
    simp only [hA] at t
    exact (Metric.tendsto_nhds.1 t ε hε).mono fun y hy => by rwa [dist_eq_norm] at hy
  have e3 : ∀ᶠ y in 𝓝 ((p0, r0) : K × K), ‖cBq Δ a b y.1 y.2‖ < ε := by
    have t := hB'.tendsto
    simp only [hB] at t
    exact (Metric.tendsto_nhds.1 t ε hε).mono fun y hy => by rwa [dist_zero_right] at hy
  obtain ⟨η, hη, hball⟩ := Metric.eventually_nhds_iff.1 (e1.and (e2.and e3))
  refine ⟨η, hη, fun p r hp hr => ?_⟩
  have hd : dist ((p, r) : K × K) (p0, r0) < η := by
    rw [Prod.dist_eq, max_lt_iff, dist_eq_norm, dist_eq_norm]; exact ⟨hp, hr⟩
  obtain ⟨h1, h2, h3⟩ := hball hd
  exact ⟨h1, h2, h3⟩

theorem loc_near (Δ a b : K) (h2 : (2 : K) ≠ 0) (hΔ : Δ ≠ 0) (hab : a * a - Δ * (b * b) = 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ p0 r0 : K, ∃ η > 0, ∀ p r : K, ‖p - p0‖ < η → ‖r - r0‖ < η →
      nrm Δ p r ≠ 0 ∧ ‖cAq Δ a b p r - 1‖ < ε ∧ ‖cBq Δ a b p r‖ < ε := by
  by_cases ha : 1 + a = 0
  · have hb : b = 0 := by
      have hbb : Δ * (b * b) = 0 := by
        have : a = -1 := by linear_combination ha
        subst this; linear_combination -hab
      exact mul_self_eq_zero.mp ((mul_eq_zero.mp hbb).resolve_left hΔ)
    have hN : nrm Δ 0 1 = -Δ := by unfold nrm; ring
    have hN0 : nrm Δ 0 1 ≠ 0 := by rw [hN]; exact neg_ne_zero.mpr hΔ
    refine ⟨0, 1, loc_of Δ a b 0 1 hN0 ?_ ?_ ε hε⟩
    · unfold cAq; rw [div_eq_one_iff_eq hN0, hN, hb]; linear_combination Δ * ha
    · unfold cBq; rw [hb]; simp
  · have hN : nrm Δ (1 + a) b = 2 * (1 + a) := by unfold nrm; linear_combination hab
    have hN0 : nrm Δ (1 + a) b ≠ 0 := by rw [hN]; exact mul_ne_zero h2 ha
    refine ⟨1 + a, b, loc_of Δ a b (1 + a) b hN0 ?_ ?_ ε hε⟩
    · unfold cAq; rw [div_eq_one_iff_eq hN0, hN]; linear_combination (a + 2) * hab
    · unfold cBq; rw [div_eq_zero_iff]; left; linear_combination (-b) * hab

end Loc

end Formalism.IndefR.Fin.U1

end
