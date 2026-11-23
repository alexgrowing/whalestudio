import Mathlib
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsLatFlagPair
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
open MvPolynomial

theorem PositivityTheory.Xgn.multihomogeneous_eval_scale : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (s : MvPolynomial (Σ k, ι k) ℤ) (a : K → ℕ) (c : K → ℂ) (z : ((Σ k, ι k) → ℂ)), GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog s a → eval (fun p => c p.1 * z p) (MvPolynomial.map (Int.castRingHom ℂ) s) = (∏ k, c k ^ a k) * eval z (MvPolynomial.map (Int.castRingHom ℂ) s) := by
  intro K _ _ ι _ s a c z hs
  rw [eval_map, eval_map, eval₂_eq', eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hw : Finsupp.weight (GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight ι) m = a :=
    hs (mem_support_iff.mp hm)
  have ha : ∀ k, a k = ∑ i : ι k, m ⟨k, i⟩ := by
    intro k
    rw [← hw, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply,
      Fintype.sum_sigma, Finset.sum_eq_single k]
    · simp [GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight]
    · intro j _ hj
      simp [GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight, Pi.single_apply, hj, hj.symm]
    · simp
  have h1 : ∏ p : (Σ k, ι k), c p.1 ^ m p = ∏ k, c k ^ a k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [ha k, ← Finset.prod_pow_eq_pow_sum]
  simp only [mul_pow]
  rw [Finset.prod_mul_distrib, h1]
  ring
