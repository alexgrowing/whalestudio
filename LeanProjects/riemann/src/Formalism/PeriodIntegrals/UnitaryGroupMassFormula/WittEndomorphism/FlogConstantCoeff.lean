import Formalism.PeriodIntegrals.W2pair
import Formalism.PeriodIntegrals.WfRing
import Formalism.PeriodIntegrals.WfSubst
import Formalism.PeriodIntegrals.InvSerSub
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExponentialIntegrality.StepIII
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExponentialIntegrality.RootsOfUnityRingLeWittIntegers

noncomputable section

namespace PI.WfEndProof

open PI

theorem flog_constantCoeff' {p : ℕ} [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) :
    PowerSeries.constantCoeff (AddIntG.flog W wq) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, AddIntG.flog, PowerSeries.coeff_mk]
  simp

theorem coefWf_X (p : ℕ) [Fact p.Prime] : CoefWf (MvPowerSeries.X () : MvPowerSeries Unit ℂ_[p]) := by
  intro n
  refine ⟨0, ?_⟩
  rw [pow_zero, one_mul, MvPowerSeries.coeff_X]
  split_ifs
  · exact (Wp p).one_mem
  · exact (Wp p).zero_mem

theorem wfEnd_of (hR : WfRing) (hS : WfSubst) (hL : WfLog) : WfEnd := by
  intro p _ W wq ex h1 h2 h3 h4 h6 hW hex hsub c hc hI n
  obtain ⟨hl, hx⟩ := hL p W wq ex h1 h2 h3 h4 h6 hW hex hsub
  have hX : CoefWf (MvPowerSeries.X () : MvPowerSeries Unit ℂ_[p]) := coefWf_X p
  have hX0 : MvPowerSeries.constantCoeff (MvPowerSeries.X () : MvPowerSeries Unit ℂ_[p]) = 0 := by simp
  have hA := hS p Unit (AddIntG.flog W wq) (MvPowerSeries.X ()) hl hX hX0
  have hB := (hR p Unit _ _ hA hA).2.2.2 c hc
  have hB0 : MvPowerSeries.constantCoeff (MvPowerSeries.C c *
      PowerSeries.subst (MvPowerSeries.X () : MvPowerSeries Unit ℂ_[p]) (AddIntG.flog W wq)) = 0 := by
    rw [map_mul, PowerSeries.constantCoeff_subst_eq_zero hX0 _ (flog_constantCoeff' W wq), mul_zero]
  have hM := hS p Unit ex _ hx hB hB0
  exact PI.ExpIntWProof.stepIII_of_key PI.ExpIntWProof.keyW p _ (hM n) (hI n)

theorem coprime_sq_sub_one (p : ℕ) [hp : Fact p.Prime] : Nat.Coprime (p ^ 2 - 1) p := by
  have hp' := hp.out
  refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp').2 ?_)
  intro h
  have h2 : p ∣ p ^ 2 := dvd_pow_self p two_ne_zero
  have h3 : p ∣ p ^ 2 - (p ^ 2 - 1) := Nat.dvd_sub h2 h
  have h4 : p ^ 2 - (p ^ 2 - 1) = 1 := by
    have : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ hp'.pos
    omega
  rw [h4] at h3
  exact hp'.one_lt.ne' (Nat.dvd_one.1 h3)

theorem pairW : PairW := by
  intro p _ α hα
  have hpos : 0 < p ^ 2 - 1 := by
    have := (Fact.out : p.Prime).two_le
    have : 4 ≤ p ^ 2 := by nlinarith
    omega
  have hle : Subring.closure {x : ℂ_[p] × ℂ_[p] | ∃ ζ : ℂ_[p], ζ ^ (p ^ 2 - 1) = 1 ∧ x = (ζ, ζ ^ p)} ≤
      (Wp p).comap (RingHom.fst ℂ_[p] ℂ_[p]) := by
    rw [Subring.closure_le]
    rintro _ ⟨ζ, hζ, rfl⟩
    show ζ ∈ (Subring.closure {ζ : ℂ_[p] | ∃ n : ℕ, 0 < n ∧ Nat.Coprime n p ∧ ζ ^ n = 1}).topologicalClosure
    exact Subring.le_topologicalClosure _ (Subring.subset_closure ⟨_, hpos, coprime_sq_sub_one p, hζ⟩)
  have hclosed : IsClosed (Prod.fst ⁻¹' (Wp p : Set ℂ_[p])) :=
    IsClosed.preimage (continuous_fst : Continuous (Prod.fst : ℂ_[p] × ℂ_[p] → ℂ_[p])) (show IsClosed (Wp p : Set ℂ_[p]) from Subring.isClosed_topologicalClosure _)
  exact closure_minimal (fun x hx => hle hx) hclosed hα

end PI.WfEndProof

end
