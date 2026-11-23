import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DiagonalPadicSubstitution.SubstOps

noncomputable section

open Classical

namespace PI.BeDiagZp.OpsW

variable {p : ℕ} [Fact p.Prime]

theorem psubst_comm {σ τ : Type} {s : σ → MvPowerSeries τ ℂ_[p]} (hs : MvPowerSeries.HasSubst s)
    (a : MvPowerSeries σ ℂ_[p]) (ha : MvPowerSeries.constantCoeff a = 0) (f : PowerSeries ℂ_[p]) :
    MvPowerSeries.subst s (PowerSeries.subst a f) = PowerSeries.subst (MvPowerSeries.subst s a) f := by
  have h1 : MvPowerSeries.HasSubst (fun _ : Unit => a) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => ha)
  rw [PowerSeries.subst_def, PowerSeries.subst_def,
    MvPowerSeries.subst_comp_subst_apply (a := fun _ : Unit => a) h1 hs f]

theorem substOps_holds : SubstOps := by
  intro p _ l ex ph hex hl σ τ _ s hs0
  have hs : MvPowerSeries.HasSubst s := MvPowerSeries.hasSubst_of_constantCoeff_zero hs0
  have cc : ∀ a : MvPowerSeries σ ℂ_[p], MvPowerSeries.constantCoeff a = 0 →
      MvPowerSeries.constantCoeff (MvPowerSeries.subst s a) = 0 :=
    fun a ha => MvPowerSeries.constantCoeff_subst_eq_zero hs hs0 ha
  refine ⟨fun i => MvPowerSeries.subst_X hs i, fun c a => ?_, fun a b => MvPowerSeries.subst_add hs a b,
    fun a b ha hb => ?_⟩
  · rw [MvPowerSeries.subst_mul hs, MvPowerSeries.subst_C]
  · have hla : MvPowerSeries.constantCoeff (PowerSeries.subst a l) = 0 :=
      PowerSeries.constantCoeff_subst_eq_zero ha l hl
    have hlb : MvPowerSeries.constantCoeff (PowerSeries.subst b l) = 0 :=
      PowerSeries.constantCoeff_subst_eq_zero hb l hl
    have hab : MvPowerSeries.constantCoeff (add l ex a b) = 0 :=
      PowerSeries.constantCoeff_subst_eq_zero (by rw [map_add, hla, hlb, add_zero]) ex hex
    have hadd : MvPowerSeries.subst s (add l ex a b) =
        add l ex (MvPowerSeries.subst s a) (MvPowerSeries.subst s b) := by
      unfold add
      rw [psubst_comm hs _ (by rw [map_add, hla, hlb, add_zero]) ex, MvPowerSeries.subst_add hs,
        psubst_comm hs a ha l, psubst_comm hs b hb l]
    refine ⟨cc a ha, hadd, fun c => ?_, psubst_comm hs a ha ph, ?_⟩
    · unfold mulBy
      rw [psubst_comm hs _ (by rw [map_mul, hla, mul_zero]) ex, MvPowerSeries.subst_mul hs,
        MvPowerSeries.subst_C, psubst_comm hs a ha l]
    · unfold be phAt
      rw [MvPowerSeries.subst_sub hs, MvPowerSeries.subst_sub hs, psubst_comm hs _ hab ph,
        psubst_comm hs a ha ph, psubst_comm hs b hb ph, hadd]

end PI.BeDiagZp.OpsW
