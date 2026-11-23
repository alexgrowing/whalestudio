import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.LogChain

set_option autoImplicit false

noncomputable section

open MvPowerSeries

namespace ReciprocityTheory.ChartRestriction.G.TB.LogPf

variable {k : Type} [CommRing k] [Algebra ℚ k] {τ : Type} [Fintype τ] [DecidableEq τ]

def prim (ω : τ → MvPowerSeries τ k) : MvPowerSeries τ k := fun m =>
  algebraMap ℚ k ((m.degree : ℚ)⁻¹) *
    ∑ w, if m w = 0 then 0 else coeff (m - Finsupp.single w 1) (ω w)

theorem coeff_prim (ω : τ → MvPowerSeries τ k) (m : τ →₀ ℕ) :
    coeff m (prim ω) = algebraMap ℚ k ((m.degree : ℚ)⁻¹) *
      ∑ w, if m w = 0 then 0 else coeff (m - Finsupp.single w 1) (ω w) := rfl

theorem constantCoeff_prim (ω : τ → MvPowerSeries τ k) : constantCoeff (prim ω) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_prim]
  simp

theorem degree_eq_sum (n : τ →₀ ℕ) : n.degree = ∑ w, n w := by
  classical
  unfold Finsupp.degree
  exact Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => by simpa using hi)

theorem pderiv_prim (ω : τ → MvPowerSeries τ k)
    (hω : ∀ a c, pderiv k c (ω a) = pderiv k a (ω c)) (v : τ) : pderiv k v (prim ω) = ω v := by
  ext m
  rw [coeff_pderiv, coeff_prim]
  set n := m + Finsupp.single v 1 with hn
  have key : ∀ w, (if n w = 0 then 0 else coeff (n - Finsupp.single w 1) (ω w)) * ((m v : k) + 1)
      = (n w : k) * coeff m (ω v) := by
    intro w
    by_cases hw : w = v
    · subst hw
      have h1 : n w = m w + 1 := by simp [hn]
      have h2 : n - Finsupp.single w 1 = m := by rw [hn]; exact add_tsub_cancel_right _ _
      rw [if_neg (by omega), h2, h1]
      push_cast
      ring
    · have h1 : n w = m w := by simp [hn, Finsupp.single_apply, hw, Ne.symm hw]
      by_cases hm : m w = 0
      · rw [if_pos (by rw [h1, hm]), h1, hm]
        simp
      · rw [if_neg (by rw [h1]; exact hm), h1]
        have hle : Finsupp.single w 1 ≤ m := Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hm)
        have hc := congrArg (coeff (m - Finsupp.single w 1)) (hω w v)
        rw [coeff_pderiv, coeff_pderiv] at hc
        have e1 : m - Finsupp.single w 1 + Finsupp.single v 1 = n - Finsupp.single w 1 := by
          rw [hn]; exact tsub_add_eq_add_tsub hle
        have e2 : m - Finsupp.single w 1 + Finsupp.single w 1 = m := tsub_add_cancel_of_le hle
        have e3 : (m - Finsupp.single w 1 : τ →₀ ℕ) v = m v := by
          simp [Finsupp.single_apply, hw, Ne.symm hw]
        have e4' : (m - Finsupp.single w 1 : τ →₀ ℕ) w + 1 = m w := by
          rw [Finsupp.tsub_apply, Finsupp.single_eq_same]; omega
        have e4 : ((m - Finsupp.single w 1 : τ →₀ ℕ) w : k) + 1 = (m w : k) := by
          rw [← e4', Nat.cast_add, Nat.cast_one]
        rw [e1, e2, e3, e4] at hc
        rw [hc]
        ring
  have hsum : (∑ w, if n w = 0 then 0 else coeff (n - Finsupp.single w 1) (ω w)) * ((m v : k) + 1)
      = (n.degree : k) * coeff m (ω v) := by
    rw [Finset.sum_mul, Finset.sum_congr rfl (fun w _ => key w), ← Finset.sum_mul, degree_eq_sum,
      Nat.cast_sum]
  have hnv : n v = m v + 1 := by simp [hn]
  have hD : (n.degree : ℚ) ≠ 0 := by
    have : n v ≤ n.degree := by
      rw [degree_eq_sum]
      exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ v)
    exact_mod_cast (show n.degree ≠ 0 by omega)
  rw [mul_assoc, hsum, ← mul_assoc, ← map_natCast (algebraMap ℚ k) n.degree, ← map_mul,
    inv_mul_cancel₀ hD, map_one, one_mul]

theorem exists_prim (ω : τ → MvPowerSeries τ k) (hω : ∀ a c, pderiv k c (ω a) = pderiv k a (ω c)) :
    ∃ ℓ : MvPowerSeries τ k, constantCoeff ℓ = 0 ∧ ∀ v, pderiv k v ℓ = ω v :=
  ⟨prim ω, constantCoeff_prim ω, pderiv_prim ω hω⟩

end ReciprocityTheory.ChartRestriction.G.TB.LogPf
