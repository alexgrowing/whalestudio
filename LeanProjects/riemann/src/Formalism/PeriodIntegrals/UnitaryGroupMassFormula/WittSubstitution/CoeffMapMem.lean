import Mathlib
import Formalism.PeriodIntegrals.WfSubst
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExponentialIntegrality.InvNatMemWf

noncomputable section

namespace PI.WfSubstProof

theorem exists_lift {A : Type} [CommRing A] (S : Subring A) {σ : Type} (f : MvPowerSeries σ A)
    (h : ∀ e, MvPowerSeries.coeff e f ∈ S) :
    ∃ g : MvPowerSeries σ S, MvPowerSeries.map S.subtype g = f := by
  let g : MvPowerSeries σ S := fun e => ⟨MvPowerSeries.coeff e f, h e⟩
  refine ⟨g, ?_⟩
  ext e
  rw [MvPowerSeries.coeff_map]
  rfl

theorem coeff_map_mem {A : Type} [CommRing A] (S : Subring A) {σ : Type} (g : MvPowerSeries σ S)
    (e : σ →₀ ℕ) : MvPowerSeries.coeff e (MvPowerSeries.map S.subtype g) ∈ S := by
  rw [MvPowerSeries.coeff_map]
  exact (MvPowerSeries.coeff e g).2

theorem substSub : PI.SubstSub := by
  intro A _ S σ f a hf ha ha0 n
  have hf' : ∀ e : Unit →₀ ℕ, MvPowerSeries.coeff e f ∈ S := fun e => by
    have he : e = Finsupp.single () (e ()) := by
      ext
      simp
    rw [he]
    exact hf (e ())
  obtain ⟨fS, rfl⟩ := exists_lift S f hf'
  obtain ⟨aS, rfl⟩ := exists_lift S a ha
  have haS0 : MvPowerSeries.constantCoeff aS = 0 := by
    have h0 := ha0
    rw [MvPowerSeries.constantCoeff_map] at h0
    exact Subtype.val_injective h0
  have hsub : PowerSeries.HasSubst aS := PowerSeries.HasSubst.of_constantCoeff_zero haS0
  have key : PowerSeries.subst (MvPowerSeries.map S.subtype aS) (MvPowerSeries.map S.subtype fS : PowerSeries A) =
      MvPowerSeries.map S.subtype (PowerSeries.subst aS fS) :=
    (PowerSeries.map_subst hsub fS).symm
  rw [key]
  exact coeff_map_mem S _ n

theorem wfSubst : PI.WfSubst := by
  intro p _ σ f a hf ha ha0 n
  have h := substSub ℂ_[p] (ExpIntWProof.Wf p) σ f a (fun m => ExpIntWProof.mem_Wf.2 (hf _))
    (fun m => ExpIntWProof.mem_Wf.2 (ha m)) ha0
  exact ExpIntWProof.mem_Wf.1 (h n)

end PI.WfSubstProof
