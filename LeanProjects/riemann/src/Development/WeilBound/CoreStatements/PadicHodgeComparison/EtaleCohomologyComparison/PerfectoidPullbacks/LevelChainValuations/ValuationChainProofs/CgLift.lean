import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.ChainOf
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.IsProperOfProj
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.BcOnFalse
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DividedPowerReduction.CoefficientReductionFirstChernClassTateTwist
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ChartGrConst
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.SmoothGaloisGeometry.NormLtOneOfIrreducible

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb.Kap

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {R : Per l K} {m : ℕ}

namespace DividedPowerLiftFacts

theorem l_ne_zero : ((l : ℕ) : OK l K) ≠ 0 := by
  intro h
  have h1 := congrArg (fun z : OK l K => ((z : K) : PadicAlgCl l)) h
  have h2 : ((l : ℕ) : PadicAlgCl l) = 0 := by simpa using h1
  exact (Fact.out : l.Prime).ne_zero (by exact_mod_cast h2)

theorem dividedPowerFiltration_bot (r : ℕ) (hr : 1 ≤ r) : pdP (dividedPowersBot (OK l K)) r = ⊥ := by
  unfold pdP
  rw [Ideal.span_eq_bot]
  rintro z ⟨L, hL, hs, rfl⟩
  have hpos : 0 < (List.map Prod.fst L).sum := lt_of_lt_of_le hr hs
  obtain ⟨q, hq, hq0⟩ : ∃ q ∈ L, q.1 ≠ 0 := by
    by_contra hc
    push Not at hc
    have : (List.map Prod.fst L).sum = 0 := List.sum_eq_zero (by
      intro x hx
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hx
      exact hc q hq)
    omega
  apply List.prod_eq_zero
  refine List.mem_map.2 ⟨q, hq, ?_⟩
  have h2 : q.2 = 0 := (Ideal.mem_bot).1 (hL q hq)
  rw [h2]
  exact dpow_eval_zero _ hq0

theorem dividedPowerFiltration_zero : pdP (dividedPowersBot (OK l K)) 0 = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  unfold pdP
  exact Ideal.subset_span ⟨[], by simp, by simp, by simp⟩

theorem divides [FiniteDimensional ℚ_[l] K] (a : OK l K) (ha : a ≠ 0) : ∃ k : ℕ, a ∣ (l : OK l K) ^ k := by
  have := OK_dvr (l := l) (K := K)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (OK l K)
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible ha hϖ
  have hlm : ((l : ℕ) : OK l K) ∈ IsLocalRing.maximalIdeal (OK l K) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_OK_iff]
    have e : (((((l : ℕ) : OK l K) : K)) : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by simp
    rw [e, PadicAlgCl.norm_extends]
    exact Padic.norm_p_lt_one.ne
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.mem_span_singleton] at hlm
  exact ⟨n, hn.dvd.trans (pow_dvd_pow_of_dvd hlm n)⟩

end DividedPowerLiftFacts

open DividedPowerLiftFacts in
theorem cg_lift_pf [FiniteDimensional ℚ_[l] K] {L : Lev R m} (hL : L.Good) (M : Model l K) (hM : M.Sm) (s : ℕ) (hs : m ≤ s)
    (j : ℕ) : ∃ e : ℕ, LiftP (QA L M s) (l : L.A) s j e := by
  have hdvr : IsDiscreteValuationRing (OK l K) := OK_dvr
  have hdiv : ∀ a : OK l K, a ≠ 0 → ∃ k : ℕ, a ∣ (l : OK l K) ^ k := divides
  have hs1 : 1 ≤ s := le_trans hL.pos hs
  have htf : TFBase (dividedPowersBot (OK l K)) l s :=
    { nil := dividedPowerFiltration_bot s hs1
      tf := by
        intro r x hx
        rcases Nat.eq_zero_or_pos r with rfl | hr
        · rw [dividedPowerFiltration_zero]; exact Submodule.mem_top
        · rw [dividedPowerFiltration_bot r hr, Ideal.mem_bot] at hx ⊢
          exact (mul_eq_zero.1 hx).resolve_left l_ne_zero
      dv := by
        intro n hn
        have hn' : ((n : ℕ) : OK l K) ≠ 0 := by
          intro h
          have h1 := congrArg (fun z : OK l K => ((z : K) : PadicAlgCl l)) h
          have h2 : ((n : ℕ) : PadicAlgCl l) = 0 := by simpa using h1
          exact hn (by exact_mod_cast h2)
        obtain ⟨k, u, hu⟩ := hdiv _ hn'
        exact ⟨k, u, hu.symm⟩ }
  have : IsProper M.p := sm_proper hM
  obtain ⟨U⟩ := (cov_ex M.p).1 hM.2
  exact liftA (O := OK l K) (A := L.A) L.γ l s s hdiv htf (hL.lat s hs) le_rfl
    M.p U {⊤} sSup_singleton j

end CrystallineSemistableComparison.Pb.Kap
