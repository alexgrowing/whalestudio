import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EndoZInstance

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.F

open PowerSeries

namespace TaylorWp

def T (f : ℂ → ℂ) (F : PowerSeries ℂ) : Prop := AnalyticAt ℂ f 0 ∧ taylor0 f = F

theorem T.add (hr : TaylorRing) {f g : ℂ → ℂ} {F G : PowerSeries ℂ} (hf : T f F) (hg : T g G) :
    T (fun z => f z + g z) (F + G) :=
  ⟨hf.1.add hg.1, by rw [(hr.1 f g hf.1 hg.1).1, hf.2, hg.2]⟩

theorem T.mul (hr : TaylorRing) {f g : ℂ → ℂ} {F G : PowerSeries ℂ} (hf : T f F) (hg : T g G) :
    T (fun z => f z * g z) (F * G) :=
  ⟨hf.1.mul hg.1, by rw [(hr.1 f g hf.1 hg.1).2, hf.2, hg.2]⟩

theorem T.const (hr : TaylorRing) (c : ℂ) : T (fun _ => c) (C c) :=
  ⟨analyticAt_const, hr.2.1 c⟩

theorem T.id (hr : TaylorRing) : T (fun z => z) X :=
  ⟨analyticAt_id, hr.2.2.1⟩

theorem T.pow (hr : TaylorRing) {f : ℂ → ℂ} {F : PowerSeries ℂ} (hf : T f F) (k : ℕ) :
    T (fun z => f z ^ k) (F ^ k) := by
  induction k with
  | zero => simpa using T.const hr 1
  | succ k ih => simpa only [pow_succ] using T.mul hr ih hf

end TaylorWp

open TaylorWp

theorem weierstrass_p_series_coeff : PSeriesCoeff := by
  intro L n
  rw [pSeries, taylor0, coeff_mk, L.iteratedDeriv_weierstrassPExcept_self 0]
  by_cases hn : n = 0
  · simp [hn]
  · simp only [hn, if_false, PeriodPair.sumInvPow_zero]
    have h : ((n.factorial : ℕ) : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    rw [Nat.factorial_succ]
    push_cast
    field_simp

theorem taylorIsWp_of (hr : TaylorRing) (hd : TaylorDeriv) : TaylorIsWp := by
  intro L
  refine ⟨?_, ?_, ?_⟩
  · rw [← coeff_zero_eq_constantCoeff_apply, weierstrass_p_series_coeff L 0]; simp
  · intro n hn
    rw [weierstrass_p_series_coeff L n, L.G_eq_zero_of_odd (n + 2) (by
      obtain ⟨k, rfl⟩ := hn; exact ⟨k + 1, by ring⟩)]
    simp
  · have hp : T (L.weierstrassPExcept 0) (pSeries L) := ⟨L.analyticAt_weierstrassPExcept 0, rfl⟩
    have hp' : T (deriv (L.weierstrassPExcept 0)) (Formalism.L2.Th1.B.dz (pSeries L)) :=
      ⟨hp.1.deriv, hd.1 _ hp.1⟩
    have hq := T.add hr (T.const hr 1) (T.mul hr (T.pow hr (T.id hr) 2) hp)
    have h1 := T.pow hr (T.add hr (T.const hr (-2)) (T.mul hr (T.pow hr (T.id hr) 3) hp')) 2
    have h2 := T.add hr (T.add hr (T.mul hr (T.const hr 4) (T.pow hr hq 3))
      (T.mul hr (T.mul hr (T.const hr (-L.g₂)) (T.pow hr (T.id hr) 4)) hq))
      (T.mul hr (T.const hr (-L.g₃)) (T.pow hr (T.id hr) 6))
    have key := hr.2.2.2 _ _ (?_ : (fun z => (-2 + z ^ 3 * deriv (L.weierstrassPExcept 0) z) ^ 2)
      =ᶠ[nhds 0] fun z => 4 * (1 + z ^ 2 * L.weierstrassPExcept 0 z) ^ 3
        + -L.g₂ * z ^ 4 * (1 + z ^ 2 * L.weierstrassPExcept 0 z) + -L.g₃ * z ^ 6)
    · rw [h1.2, h2.2] at key
      simp only [map_neg, map_ofNat, map_one] at key
      rw [key]; ring
    · filter_upwards [L.compl_lattice_sdiff_singleton_mem_nhds 0] with z hz
      rw [L.eqOn_deriv_weierstrassPExcept_derivWeierstrassPExcept 0 hz]
      by_cases hz0 : z = 0
      · simp [hz0]; norm_num
      replace hz : z ∉ L.lattice := by simp_all
      have hE := L.derivWeierstrassP_sq z hz
      have e1 := L.weierstrassPExcept_def 0 z
      have e2 := L.derivWeierstrassPExcept_def 0 z
      simp only [ZeroMemClass.coe_zero, sub_zero] at e1 e2
      rw [e1, e2]
      have e3 : (z ^ 3 * L.derivWeierstrassP z) ^ 2 = z ^ 6 * (4 * L.weierstrassP z ^ 3
          - L.g₂ * L.weierstrassP z - L.g₃) := by rw [← hE]; ring
      field_simp
      simp
      linear_combination e3

theorem weierstrass_series_unique : IsWpUnique := by
  intro K _ _ g2 g3 P Q hP hQ
  obtain ⟨-, -, hP⟩ := hP
  obtain ⟨-, -, hQ⟩ := hQ
  have hX : (X : PowerSeries K) ≠ 0 := X_ne_zero
  have hdX : ∀ n : ℕ, X * derivative K ((X : PowerSeries K) ^ n) = (n : PowerSeries K) * X ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, Derivation.leibniz, smul_eq_mul, smul_eq_mul, derivative_X]
      push_cast
      linear_combination X * ih
  have main : ∀ n : ℕ, X ^ n ∣ P - Q := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      obtain ⟨E, hE⟩ := ih
      have hD : X * (derivative K P - derivative K Q)
          = X ^ n * ((n : PowerSeries K) * E + X * derivative K E) := by
        rw [← map_sub, hE, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
        linear_combination E * hdX n
      have hc : ((n : PowerSeries K) * E + X * derivative K E)
            * (-4 + X ^ 3 * (derivative K P + derivative K Q))
          = E * (4 * ((1 + X ^ 2 * P) ^ 2 + (1 + X ^ 2 * P) * (1 + X ^ 2 * Q) + (1 + X ^ 2 * Q) ^ 2)
              - C g2 * X ^ 4) := by
        apply mul_left_cancel₀ (pow_ne_zero (n + 2) hX)
        have hs := congrArg₂ (· - ·) hP hQ
        simp only [Formalism.L2.Th1.B.dz] at hs
        linear_combination hs
          - X ^ 2 * (-4 + X ^ 3 * (derivative K P + derivative K Q)) * hD
          + X ^ 2 * (4 * ((1 + X ^ 2 * P) ^ 2 + (1 + X ^ 2 * P) * (1 + X ^ 2 * Q)
              + (1 + X ^ 2 * Q) ^ 2) - C g2 * X ^ 4) * hE
      have h0 := congrArg constantCoeff hc
      simp only [map_mul, map_add, map_sub, map_neg, map_pow, map_natCast, map_ofNat, map_one,
        constantCoeff_X, constantCoeff_C] at h0
      have h1 : (4 * (n : K) + 12) * constantCoeff E = 0 := by
        linear_combination -h0
      have h2 : (4 * (n : K) + 12) ≠ 0 := by
        have : ((4 * n + 12 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        push_cast at this
        exact this
      have h3 : constantCoeff E = 0 := (mul_eq_zero.mp h1).resolve_left h2
      obtain ⟨E', rfl⟩ := X_dvd_iff.mpr h3
      exact ⟨E', by rw [hE]; ring⟩
  have hz : P - Q = 0 := by
    ext m
    rw [map_zero]
    exact X_pow_dvd_iff.mp (main (m + 1)) m (Nat.lt_succ_self m)
  exact sub_eq_zero.mp hz

end Formalism.L2.Th1.F
