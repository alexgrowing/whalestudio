import Development.AutomorphicArithmetic.Foundations.LocalLanglands.RecTTransport
import Development.DiscreteGroups.GlobalIrreducibility.DzLcIso

open ValuativeRel Filter

private theorem val_natCast_lt_one {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (g : ℕ) [Fact g.Prime] (i : ℚ_[g] ≃+* k) (hi : Continuous i) :
    valuation k (g : k) < 1 := by
  have h1 : Tendsto (fun m : ℕ => (g : ℚ_[g]) ^ m) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one Padic.norm_p_lt_one
  have hT : Tendsto (fun m : ℕ => i ((g : ℚ_[g]) ^ m)) atTop (nhds 0) := by
    have := (hi.tendsto 0).comp h1
    rwa [map_zero] at this
  have hopen : IsOpen {x : k | valuation k x < 1} := by
    simpa [Valuation.restrict_lt_one_iff] using (valuation k).isOpen_ball 1
  have hO : {x : k | valuation k x < 1} ∈ nhds (0 : k) :=
    hopen.mem_nhds (by simp)
  obtain ⟨m, hm, hm0⟩ := ((hT.eventually hO).and (eventually_gt_atTop 0)).exists
  have hm' : valuation k (g : k) ^ m < 1 := by
    have : valuation k (i ((g : ℚ_[g]) ^ m)) < 1 := hm
    rwa [map_pow, map_natCast, map_pow] at this
  by_contra hge
  exact absurd hm' (not_lt.2 (one_le_pow₀ (not_lt.1 hge)))

private theorem val_intCast_le_one {k : Type} [Field k] [ValuativeRel k] (a : ℤ) :
    valuation k (a : k) ≤ 1 :=
  (Valuation.mem_integer_iff _ _).1 (intCast_mem (valuation k).integer a)

theorem UpperTheory.Zero.LLC.isoUniq :
    UpperTheory.Zero.LLC.IsoUniq := by
  intro k _ _ _ _ _ g g' _ _ i i' hi hi'
  refine ⟨?_, fun i'' hi'' => ?_⟩
  · by_contra hne
    have hc : Nat.Coprime g g' := (Nat.coprime_primes Fact.out Fact.out).2 hne
    have hb : ((1 : ℤ) : k) = (g : k) * (Nat.gcdA g g' : k) + (g' : k) * (Nat.gcdB g g' : k) := by
      have h := Nat.gcd_eq_gcd_ab g g'
      rw [hc.gcd_eq_one] at h
      exact_mod_cast congrArg (Int.cast : ℤ → k) h
    have hv : valuation k (1 : k) < 1 := by
      have h1 : ((1 : ℤ) : k) = 1 := Int.cast_one
      rw [← h1, hb]
      refine Valuation.map_add_lt _ ?_ ?_
      · rw [map_mul]
        exact mul_lt_one_of_lt_of_le (val_natCast_lt_one g i hi) (val_intCast_le_one _)
      · rw [map_mul]
        exact mul_lt_one_of_lt_of_le (val_natCast_lt_one g' i' hi') (val_intCast_le_one _)
    rw [map_one] at hv
    exact lt_irrefl _ hv
  · have h : (i'' : ℚ_[g] → k) = i :=
      (Padic.denseRange_ratCast g).equalizer hi'' hi (by
        funext q
        simp only [Function.comp_apply, map_ratCast])
    exact DFunLike.coe_injective h
