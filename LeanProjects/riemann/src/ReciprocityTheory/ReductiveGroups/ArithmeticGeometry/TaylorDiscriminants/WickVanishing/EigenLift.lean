import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.EigenLift

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.TB

open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem beta_sesquilinear : BetaSesqSt := by
  intro R _ d O _ _ k _ _ _ B a ξ η
  simp only [betaH, OactH, star_star, Finset.sum_sub_distrib]
  congr 1
  · simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  · simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem betaH_smul_left {k : Type} [CommRing k] {d : ℕ} (c : k) (ξ η : (Fin d → k) × (Fin d → k)) :
    betaH k (c • ξ) η = c * betaH k ξ η := by
  simp only [betaH, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem betaH_smul_right {k : Type} [CommRing k] {d : ℕ} (c : k) (ξ η : (Fin d → k) × (Fin d → k)) :
    betaH k ξ (c • η) = c * betaH k ξ η := by
  simp only [betaH, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem eigen_orthogonality : EigenOrthSt := by
  intro R _ d O _ _ k _ _ _ B χ χ' ξ η hξ hη ⟨a, ha⟩
  have h := beta_sesquilinear R d O k B a ξ η
  rw [hξ a, hη (star a), betaH_smul_left, betaH_smul_right] at h
  have h2 : (χ a - χ' (star a)) * betaH k ξ η = 0 := by rw [sub_mul, h, sub_self]
  exact ha.mul_right_eq_zero.mp h2

end ReciprocityTheory.ChartRestriction.G.TB
