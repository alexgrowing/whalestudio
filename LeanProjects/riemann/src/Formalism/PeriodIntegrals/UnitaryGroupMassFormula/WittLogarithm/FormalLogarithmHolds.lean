import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WittLogarithm.CoefWfIff
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdditiveIntegralGroups.DXEqDerivative
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdditiveIntegralGroups.SubstMem

noncomputable section

namespace PI.WfLogWork

open PI.ExpIntWProof PI.AddIntG.Wk

theorem mem_SerS_iff {K : Type*} [CommRing K] (S : Subring K) (f : PowerSeries K) :
    (f : MvPowerSeries Unit K) ∈ SerS S Unit ↔ ∀ n, PowerSeries.coeff n f ∈ S := by
  rw [mem_SerS]
  constructor
  · intro h n
    exact h _
  · intro h e
    have he : e = Finsupp.single () (e ()) := by
      ext u
      simp
    rw [he]
    exact h (e ())

variable {p : ℕ} [Fact p.Prime]

theorem C_memS {S : Subring ℂ_[p]} {a : ℂ_[p]} (ha : a ∈ S) :
    ((algebraMap ℂ_[p] (PowerSeries ℂ_[p]) a : PowerSeries ℂ_[p]) : MvPowerSeries Unit ℂ_[p]) ∈ SerS S Unit := by
  rw [mem_SerS_iff]
  intro n
  rw [Algebra.algebraMap_eq_smul_one, map_smul, PowerSeries.coeff_one, smul_eq_mul]
  split_ifs <;> simp [ha]

theorem X_memS (S : Subring ℂ_[p]) :
    ((PowerSeries.X : PowerSeries ℂ_[p]) : MvPowerSeries Unit ℂ_[p]) ∈ SerS S Unit := by
  rw [mem_SerS_iff]
  intro n
  rw [PowerSeries.coeff_X]
  split_ifs <;> simp

theorem Gv_memS {S : Subring ℂ_[p]} {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]}
    (h1 : W.a₁ ∈ S) (h2 : W.a₂ ∈ S) (h3 : W.a₃ ∈ S) (h4 : W.a₄ ∈ S) (h6 : W.a₆ ∈ S) (hW : AddIntG.IsWq W wq) :
    ((Gv W (PowerSeries.X : PowerSeries ℂ_[p]) (wser wq) : PowerSeries ℂ_[p]) : MvPowerSeries Unit ℂ_[p]) ∈
      SerS S Unit := by
  have hC : ∀ {a : ℂ_[p]}, a ∈ S →
      ((algebraMap ℂ_[p] (PowerSeries ℂ_[p]) a : PowerSeries ℂ_[p]) : MvPowerSeries Unit ℂ_[p]) ∈
        SerS S Unit := fun ha => C_memS ha
  have hX := X_memS (p := p) S
  have hw : (wq : MvPowerSeries Unit ℂ_[p]) ∈ SerS S Unit :=
    (mem_SerS_iff S wq).2 (wq_mem h1 h2 h3 h4 h6 hW)
  have h2m : (2 : MvPowerSeries Unit ℂ_[p]) ∈ SerS S Unit := by
    simpa using natCast_mem (SerS S Unit) 2
  have h3m : (3 : MvPowerSeries Unit ℂ_[p]) ∈ SerS S Unit := by
    simpa using natCast_mem (SerS S Unit) 3
  have hv := mul_mem (pow_mem hX 3) hw
  simp only [Gv, wser]
  exact sub_mem (add_mem (add_mem (add_mem (add_mem (mul_mem (hC h1) hX)
    (mul_mem (hC h2) (pow_mem hX 2))) (mul_mem (mul_mem h2m (hC h3)) hv))
    (mul_mem (mul_mem (mul_mem h2m (hC h4)) hX) hv))
    (mul_mem (mul_mem h3m (hC h6)) (pow_mem hv 2))) (one_mem _)

theorem omega_eq {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]} (hW : AddIntG.IsWq W wq) :
    AddIntG.omegaW W wq = (-Gv W (PowerSeries.X : PowerSeries ℂ_[p]) (wser wq))⁻¹ := by
  have h := omega_mul_Gv hW
  have hc : PowerSeries.constantCoeff (-Gv W (PowerSeries.X : PowerSeries ℂ_[p]) (wser wq)) ≠ 0 := by
    intro h0
    have e := congrArg PowerSeries.constantCoeff h
    rw [map_mul, map_neg, map_one] at e
    rw [map_neg, neg_eq_zero] at h0
    rw [h0, mul_zero] at e
    exact one_ne_zero (neg_eq_zero.1 e.symm)
  rw [PowerSeries.eq_inv_iff_mul_eq_one hc, mul_neg, h, neg_neg]

theorem omega_coeff_mem {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]}
    (h1 : W.a₁ ∈ Wp p) (h2 : W.a₂ ∈ Wp p) (h3 : W.a₃ ∈ Wp p) (h4 : W.a₄ ∈ Wp p) (h6 : W.a₆ ∈ Wp p)
    (hW : AddIntG.IsWq W wq) (n : ℕ) : PowerSeries.coeff n (AddIntG.omegaW W wq) ∈ Wp p := by
  have hG := Gv_memS h1 h2 h3 h4 h6 hW
  have hc : PowerSeries.constantCoeff (-Gv W (PowerSeries.X : PowerSeries ℂ_[p]) (wser wq)) = 1 := by
    simp [Gv, wser]
  have hinv := inv_mem_SerS (Wp p)
    (f := ((-Gv W (PowerSeries.X : PowerSeries ℂ_[p]) (wser wq) : PowerSeries ℂ_[p]) :
      MvPowerSeries Unit ℂ_[p])) hc (neg_mem hG)
  rw [omega_eq hW]
  exact (mem_SerS_iff (Wp p) _).1 hinv n

theorem formal_logarithm_holds : PI.WfLogL := by
  intro p _ W wq h1 h2 h3 h4 h6 hW
  rw [coefWf_iff]
  intro n
  rw [AddIntG.flog, PowerSeries.coeff_mk]
  split_ifs with hn
  · exact zero_mem _
  · rw [div_eq_mul_inv]
    exact mul_mem (Wp_le_Wf (omega_coeff_mem h1 h2 h3 h4 h6 hW (n - 1))) (inv_nat_mem_Wf p n hn)

end PI.WfLogWork
