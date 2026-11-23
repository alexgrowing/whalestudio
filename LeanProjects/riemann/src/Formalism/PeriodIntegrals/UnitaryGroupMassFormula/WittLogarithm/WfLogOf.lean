import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WittLogarithm.CoefWfIff
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdditiveIntegralGroups.GlueHoldsVar

noncomputable section

namespace PI.WfLogWork

open PI.ExpIntWProof

theorem wfLog_of (hI : PI.InvSerSub) (hL : PI.WfLogL) : PI.WfLog := by
  intro p _ W wq ex h1 h2 h3 h4 h6 hq hex hsub
  have hfl : CoefWf (AddIntG.flog W wq) := hL p W wq h1 h2 h3 h4 h6 hq
  refine ⟨hfl, ?_⟩
  have hw0 : PowerSeries.constantCoeff wq = 1 := by
    simp only [AddIntG.IsWq] at hq
    have h := congrArg PowerSeries.constantCoeff hq
    simpa using h
  have hc0 : PowerSeries.constantCoeff (AddIntG.flog W wq) = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, AddIntG.flog, PowerSeries.coeff_mk]
    simp
  have hc1 : PowerSeries.coeff 1 (AddIntG.flog W wq) = 1 := by
    clear hI hL h1 h2 h3 h4 h6 hex hsub hfl hc0 hq
    rw [AddIntG.flog, PowerSeries.coeff_mk]
    simp only [one_ne_zero, if_false, Nat.sub_self, Nat.cast_one, div_one,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, AddIntG.omegaW]
    rw [map_mul, PowerSeries.constantCoeff_inv]
    simp [hw0]
    rw [map_ofNat]
    norm_num
  let S : Subring ℂ_[p] :=
    { carrier := {x | InWf x}
      mul_mem' := by
        rintro a b ⟨k, hk⟩ ⟨k', hk'⟩
        refine ⟨k + k', ?_⟩
        have e : (p : ℂ_[p]) ^ (k + k') * (a * b) = ((p : ℂ_[p]) ^ k * a) * ((p : ℂ_[p]) ^ k' * b) := by
          ring
        rw [e]
        exact (Wp p).mul_mem hk hk'
      one_mem' := ⟨0, by simpa using (Wp p).one_mem⟩
      add_mem' := by
        rintro a b ⟨k, hk⟩ ⟨k', hk'⟩
        refine ⟨k + k', ?_⟩
        have e : (p : ℂ_[p]) ^ (k + k') * (a + b) =
            (p : ℂ_[p]) ^ k' * ((p : ℂ_[p]) ^ k * a) + (p : ℂ_[p]) ^ k * ((p : ℂ_[p]) ^ k' * b) := by
          ring
        rw [e]
        exact (Wp p).add_mem ((Wp p).mul_mem ((Wp p).pow_mem (natCast_mem (Wp p) p) _) hk)
          ((Wp p).mul_mem ((Wp p).pow_mem (natCast_mem (Wp p) p) _) hk')
      zero_mem' := ⟨0, by simpa using (Wp p).zero_mem⟩
      neg_mem' := by
        rintro a ⟨k, hk⟩
        exact ⟨k, by rw [mul_neg]; exact (Wp p).neg_mem hk⟩ }
  have hres := hI ℂ_[p] S (AddIntG.flog W wq) ex (fun n => hfl (Finsupp.single () n)) hc0 hc1 hex hsub
  intro n
  have hn : n = Finsupp.single () (n ()) := by
    ext
    simp
  rw [hn]
  exact hres (n ())

end PI.WfLogWork
