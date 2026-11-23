import Development.AbelianVarietyTheory.Definitions.Foundations.ShCocOn
import Development.AbelianVarietyTheory.Definitions.Foundations.IsLocallyConstantCycMod
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KA
open scoped Matrix

namespace GlobalTheory

theorem algebraMap_padicInt_qbar_continuous (l : ℕ) [Fact l.Prime] :
    Continuous (algebraMap ℤ_[l] (Qbar l)) := by
  rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] (Qbar l)]
  exact (continuous_algebraMap ℚ_[l] (Qbar l)).comp (by exact continuous_subtype_val)

theorem Coef.isCompact_O (l : ℕ) [Fact l.Prime] (c : Coef l) :
    IsCompact ((c.O : Set (Qbar l))) := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' ℤ_[l] c.O
  have hg : Continuous (fun v : Fin n → ℤ_[l] => ((f v : c.O) : Qbar l)) := by
    have h : (fun v : Fin n → ℤ_[l] => ((f v : c.O) : Qbar l)) =
        fun v => ∑ i, algebraMap ℤ_[l] (Qbar l) (v i) *
          ((f (fun j => if i = j then 1 else 0) : c.O) : Qbar l) := by
      funext v
      rw [LinearMap.pi_apply_eq_sum_univ f v]
      simp [Algebra.smul_def]
    rw [h]
    refine continuous_finset_sum _ (fun i _ => ?_)
    exact ((algebraMap_padicInt_qbar_continuous l).comp (continuous_apply i)).mul continuous_const
  have hrange : Set.range (fun v : Fin n → ℤ_[l] => ((f v : c.O) : Qbar l)) = (c.O : Set (Qbar l)) := by
    ext x
    constructor
    · rintro ⟨v, rfl⟩
      exact (f v).2
    · intro hx
      obtain ⟨v, hv⟩ := hf ⟨x, hx⟩
      exact ⟨v, by simp [hv]⟩
  rw [← hrange]
  exact isCompact_range hg

theorem norm_natCast_prime_qbar (l : ℕ) [Fact l.Prime] :
    ‖((l : ℕ) : Qbar l)‖ < 1 := by
  have h : ((l : ℕ) : Qbar l) = algebraMap ℚ_[l] (Qbar l) (l : ℚ_[l]) := by simp
  rw [h, PadicAlgCl.norm_extends]
  exact Padic.norm_p_lt_one

theorem coef_limit (l : ℕ) [Fact l.Prime] (c : Coef l) (a : ℕ → Qbar l)
    (ha : ∀ r, a r ∈ c.O) (hstep : ∀ r, ‖a (r + 1) - a r‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖) :
    ∃ b ∈ c.O, ∀ r, ‖b - a r‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖ := by
  set q : ℝ := ‖((l : ℕ) : Qbar l)‖ with hq
  have hq1 : q < 1 := norm_natCast_prime_qbar l
  have hq0 : 0 ≤ q := norm_nonneg _
  have hstep' : ∀ r, ‖a (r + 1) - a r‖ ≤ q ^ r := fun r => by simpa [norm_pow] using hstep r

  have htail : ∀ N k, ‖a (N + k) - a N‖ ≤ q ^ N := by
    intro N k
    induction k with
    | zero => simpa using pow_nonneg hq0 N
    | succ k ih =>
      have e : a (N + (k + 1)) - a N = (a (N + k + 1) - a (N + k)) + (a (N + k) - a N) := by
        rw [← add_assoc]; abel
      rw [e]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ih)
      exact (hstep' (N + k)).trans (pow_le_pow_of_le_one hq0 hq1.le (Nat.le_add_right N k))
  have htail' : ∀ N n, N ≤ n → ‖a n - a N‖ ≤ q ^ N := by
    intro N n hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    exact htail N k
  have hcau : CauchySeq a := by
    refine cauchySeq_of_le_tendsto_0 (fun N => q ^ N) (fun n m N hn hm => ?_)
      (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1)
    rw [dist_eq_norm]
    have e : a n - a m = (a n - a N) + -(a m - a N) := by abel
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (htail' N n hn) ?_)
    rw [norm_neg]; exact htail' N m hm
  obtain ⟨b, hb, hlim⟩ := cauchySeq_tendsto_of_isComplete (GlobalTheory.Coef.isCompact_O l c).isComplete ha hcau
  refine ⟨b, hb, fun r => ?_⟩
  have hmem : b ∈ Metric.closedBall (a r) (q ^ r) := by
    refine Metric.isClosed_closedBall.mem_of_tendsto hlim ?_
    filter_upwards [Filter.eventually_ge_atTop r] with n hn
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact htail' r n hn
  rw [Metric.mem_closedBall, dist_eq_norm] at hmem
  simpa [norm_pow] using hmem

end GlobalTheory
