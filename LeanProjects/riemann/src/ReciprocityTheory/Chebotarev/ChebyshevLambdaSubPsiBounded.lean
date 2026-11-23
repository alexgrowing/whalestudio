import ReciprocityTheory.Chebotarev.CasimirPowerSurjectiveSymmetric
import ReciprocityTheory.Chebotarev.EulerSum
import ReciprocityTheory.Chebotarev.EulerLim
import ReciprocityTheory.Chebotarev.PrimeSum
import ReciprocityTheory.Chebotarev.PrimeCont
import ReciprocityTheory.Chebotarev.PrimeAsymp

open NumberField Filter Topology

namespace ReciprocityTheory.Cheb

theorem ehold_norm_cpow (n : ℕ) {s : ℝ} (hs : 1 < s) : ‖((n : ℂ) ^ (-(s : ℂ)))‖ = (n : ℝ) ^ (-s) := by
  rw [Complex.norm_natCast_cpow_of_re_ne_zero n (by simp; linarith)]
  simp

theorem ehold_summable {E : Type} [Field E] [NumberField E] (f : NZIdeal E → ℂ) (hf : ∀ a, ‖f a‖ ≤ 1)
    {s : ℝ} (hs : 1 < s) :
    Summable (fun a : NZIdeal E => ‖f a * ((Ideal.absNorm a.1 : ℕ) : ℂ) ^ (-(s : ℂ))‖) := by
  refine (summable_absNorm_rpow E hs).of_nonneg_of_le (fun a => norm_nonneg _) (fun a => ?_)
  rw [norm_mul, ehold_norm_cpow _ hs]
  exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg _) _) (hf a)

theorem chebyshev_first_estimate : E1 := by
  refine ⟨fun E _ _ f hf s hs => (ehold_summable f hf hs).of_norm, fun E _ _ s hs => dedekindZeta_eq_tsum E hs,
    fun E _ _ s hs => summable_prm_rpow E hs⟩

theorem chebyshev_second_estimate : E2 := by
  intro E _ _ l _ χ s hs
  have key := euler_exp_log (E := E)
    (fun a => χ ((Ideal.absNorm a : ℕ) : ZMod l) * ((Ideal.absNorm a : ℕ) : ℂ) ^ (-(s : ℂ)))
    (by simp) (fun a b => by
      simp only [map_mul, Nat.cast_mul, Complex.natCast_mul_natCast_cpow]; ring)
    (ehold_summable (fun a => χ ((Ideal.absNorm a.1 : ℕ) : ZMod l)) (fun a => DirichletCharacter.norm_le_one χ _) hs)
    (fun q => by
      rw [norm_mul, ehold_norm_cpow _ hs]
      have h2 : (2 : ℝ) ≤ ((Ideal.absNorm q.asIdeal : ℕ) : ℝ) := by exact_mod_cast two_le_Nrm q
      have h3 : ((Ideal.absNorm q.asIdeal : ℕ) : ℝ) ^ (-s) < 1 :=
        Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by linarith)
      calc _ ≤ 1 * ((Ideal.absNorm q.asIdeal : ℕ) : ℝ) ^ (-s) :=
            mul_le_mul_of_nonneg_right (DirichletCharacter.norm_le_one χ _) (Real.rpow_nonneg (by positivity) _)
        _ < 1 := by rw [one_mul]; exact h3)
  exact key

theorem affine_proper_base_change : E1 := chebyshev_first_estimate

theorem proper_base_change : E2 := chebyshev_second_estimate

theorem casimirPower_surjective_symmetric : CasimirPowerSurjectiveSymmetric := casimirPower_surjective_symmetric'

theorem chebyshev_log_bounded : faceMap_castSucc_comp_eq_succ := pe_log_bdd

theorem smoothMap_seminorm_bound : SmoothMapSeminormBound := smoothMap_seminorm_bound'

end ReciprocityTheory.Cheb
