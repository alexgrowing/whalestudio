import Formalism.LocalToGlobal.InertKernelTheory.OneCopyTh1S
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.MMRead

noncomputable section

namespace Formalism.L2.KerInert

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker Classical

open ParameterChangeLemmas IntegralOrthonormalChange

theorem change_of_parameters_const_scale : ReadChangeS := by
  intro D p _ hp lam Λ C wq ph h Uu κ hph0 h0 hhi h1 hlog hUu hexp r v e F hInt
  obtain ⟨g, g0, gI, hg⟩ := exists_inv h h0 hhi h1
  have hp2 : p ≠ 2 := by omega
  obtain ⟨S, hSi⟩ : ∃ S : Fin r → MvPowerSeries D.what₂.Tau ℂ_[p],
      ∀ i, S i = PowerSeries.subst (MvPowerSeries.X (e.symm i) : MvPowerSeries D.what₂.Tau ℂ_[p]) h :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨S', hS'i⟩ : ∃ S' : D.what₂.Tau → MvPowerSeries (Fin r) ℂ_[p],
      ∀ j, S' j = PowerSeries.subst (MvPowerSeries.X (e j) : MvPowerSeries (Fin r) ℂ_[p]) g :=
    ⟨_, fun _ => rfl⟩
  have hS0 : ∀ i, MvPowerSeries.constantCoeff (S i) = 0 := fun i => by rw [hSi]; exact constantCoeff_inVar_eq_zero _ h h0
  have hS'0 : ∀ j, MvPowerSeries.constantCoeff (S' j) = 0 := fun j => by rw [hS'i]; exact constantCoeff_inVar_eq_zero _ g g0
  have hSs : MvPowerSeries.HasSubst S := MvPowerSeries.hasSubst_of_constantCoeff_zero hS0
  have hS's : MvPowerSeries.HasSubst S' := MvPowerSeries.hasSubst_of_constantCoeff_zero hS'0
  have hh : PowerSeries.HasSubst h := PowerSeries.HasSubst.of_constantCoeff_zero' h0
  have hgs : PowerSeries.HasSubst g := PowerSeries.HasSubst.of_constantCoeff_zero' g0
  have hl0 := flog_constantCoeff (C • wModel lam Λ) wq

  have hA : MvPowerSeries.subst S (atLogV D lam Λ C wq v (liftT D F)) =
      ReadTh1 p (fun τ j => κ * v (e j) (τ, 0, 0)) F := by
    have hXfl : ∀ i : Fin r, MvPowerSeries.constantCoeff (PowerSeries.subst
        (MvPowerSeries.X i : MvPowerSeries (Fin r) ℂ_[p]) (flog (C • wModel lam Λ) wq)) = 0 :=
      fun i => constantCoeff_inVar_eq_zero i _ hl0
    have hΦ : MvPowerSeries.HasSubst (fun k : D.what₂.Tau × Fin 1 × Fin 1 =>
        ∑ i, algebraMap ℂ_[p] (MvPowerSeries (Fin r) ℂ_[p]) (((C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * v i k) *
          PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin r) ℂ_[p]) (flog (C • wModel lam Λ) wq)) := by
      apply MvPowerSeries.hasSubst_of_constantCoeff_zero
      intro k
      simp [map_sum, hXfl]
    have hΦ' : MvPowerSeries.HasSubst (fun τ : D.what₂.Tau =>
        ∑ i, algebraMap ℂ_[p] (MvPowerSeries (Fin r) ℂ_[p]) (((C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * v i (τ, 0, 0)) *
          PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin r) ℂ_[p]) (flog (C • wModel lam Λ) wq)) := by
      apply MvPowerSeries.hasSubst_of_constantCoeff_zero
      intro k
      simp [map_sum, hXfl]
    have hL : MvPowerSeries.HasSubst (fun τ : D.what₂.Tau =>
        (MvPowerSeries.X (τ, 0, 0) : MvPowerSeries (D.what₂.Tau × Fin 1 × Fin 1) ℂ_[p])) :=
      MvPowerSeries.hasSubst_of_constantCoeff_zero (fun τ => MvPowerSeries.constantCoeff_X _)
    unfold atLogV liftT ReadTh1
    try dsimp only
    rw [MvPowerSeries.subst_comp_subst_apply hL hΦ]
    simp only [MvPowerSeries.subst_X hΦ]
    rw [MvPowerSeries.subst_comp_subst_apply hΦ' hSs]
    congr 1
    funext τ
    rw [← MvPowerSeries.coe_substAlgHom hSs, map_sum]
    simp only [map_mul, AlgHom.commutes, MvPowerSeries.coe_substAlgHom, subst_single_var S hSs]
    refine (Fintype.sum_equiv e _ _ fun j => ?_).symm
    rw [hSi, e.symm_apply_apply, ← PowerSeries.subst_comp_subst_apply hh (PowerSeries.HasSubst.X j)]
    unfold Formalism.InvariantFactorPaths.G7.at1
    have key := congrArg (PowerSeries.subst (MvPowerSeries.X j : MvPowerSeries D.what₂.Tau ℂ_[p])) hlog
    rw [PowerSeries.subst_mul (PowerSeries.HasSubst.X j), PowerSeries.subst_mul (PowerSeries.HasSubst.X j),
      PowerSeries.subst_C, PowerSeries.subst_C] at key
    have hid : ∀ x : ℂ_[p], algebraMap ℂ_[p] ℂ_[p] x = x := fun _ => rfl
    simp only [MvPowerSeries.algebraMap_apply, hid] at key ⊢
    first
      | linear_combination (MvPowerSeries.C (v (e j) (τ, 0, 0)) : MvPowerSeries D.what₂.Tau ℂ_[p]) * key
      | linear_combination (-(MvPowerSeries.C (v (e j) (τ, 0, 0)) : MvPowerSeries D.what₂.Tau ℂ_[p])) * key

  have hB : MvPowerSeries.subst S (ePh lam Λ C wq r) =
      (∏ j, PowerSeries.subst (MvPowerSeries.X j : MvPowerSeries D.what₂.Tau ℂ_[p]) Uu) *
        Formalism.DworkPowerSeriesWeights.mvExp (Formalism.L2.Th1.E.phSum ph : MvPowerSeries D.what₂.Tau ℂ_[p]) := by
    have hfac : ∀ i : Fin r, MvPowerSeries.subst S
        (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin r) ℂ_[p]) (ePhi1 lam Λ C wq))⁻¹ =
        PowerSeries.subst (MvPowerSeries.X (e.symm i) : MvPowerSeries D.what₂.Tau ℂ_[p])
          (Uu * (Formalism.DworkPowerSeriesWeights.mvExp ph : PowerSeries ℂ_[p])) := by
      intro i
      rw [← subst_inv _ (MvPowerSeries.constantCoeff_X i) (ePhi1 lam Λ C wq), subst_single_var S hSs, hSi,
        ← PowerSeries.subst_comp_subst_apply hh (PowerSeries.HasSubst.X _), hexp]
    unfold ePh
    rw [if_neg hp2, ← MvPowerSeries.coe_substAlgHom hSs, map_prod]
    simp only [MvPowerSeries.coe_substAlgHom, hfac]
    rw [Fintype.prod_equiv e.symm
      (fun i => PowerSeries.subst (MvPowerSeries.X (e.symm i) : MvPowerSeries D.what₂.Tau ℂ_[p])
        (Uu * (Formalism.DworkPowerSeriesWeights.mvExp ph : PowerSeries ℂ_[p])))
      (fun j => PowerSeries.subst (MvPowerSeries.X j : MvPowerSeries D.what₂.Tau ℂ_[p])
        (Uu * (Formalism.DworkPowerSeriesWeights.mvExp ph : PowerSeries ℂ_[p]))) (fun _ => rfl)]
    simp only [PowerSeries.subst_mul (PowerSeries.HasSubst.X _)]
    rw [Finset.prod_mul_distrib]
    congr 1
    have hph : ∀ j : D.what₂.Tau, MvPowerSeries.constantCoeff
        (PowerSeries.subst (MvPowerSeries.X j : MvPowerSeries D.what₂.Tau ℂ_[p]) ph) = 0 :=
      fun j => constantCoeff_inVar_eq_zero j ph hph0
    change _ = Formalism.L2.Th1.C.mvExp (∑ j, PowerSeries.subst (MvPowerSeries.X j : MvPowerSeries D.what₂.Tau ℂ_[p]) ph)
    rw [Formalism.L2.Th1.C.mvExp_sum _ _ (fun j _ => hph j)]
    refine Finset.prod_congr rfl fun j _ => ?_
    exact Formalism.L2.Th1.C.subst_mvExp hph0 (MvPowerSeries.constantCoeff_X j)

  have hSG : IntegralMv (MvPowerSeries.subst S (atLogV D lam Λ C wq v (liftT D F) * ePh lam Λ C wq r)) := by
    rw [← MvPowerSeries.coe_substAlgHom hSs, map_mul, MvPowerSeries.coe_substAlgHom, hA, hB]
    have hInt' : IntegralMv (Formalism.DworkPowerSeriesWeights.mvExp (Formalism.L2.Th1.E.phSum ph : MvPowerSeries D.what₂.Tau ℂ_[p]) *
        ReadTh1 p (fun τ j => κ * v (e j) (τ, 0, 0)) F) := hInt
    have hU : IntegralMv (∏ j, PowerSeries.subst (MvPowerSeries.X j : MvPowerSeries D.what₂.Tau ℂ_[p]) Uu) :=
      integral_prod _ _ fun j _ => integral_subst_single_variable j Uu hUu
    have := integral_mul hU hInt'
    convert this using 1
    ring

  have hback : MvPowerSeries.subst S' (MvPowerSeries.subst S
      (atLogV D lam Λ C wq v (liftT D F) * ePh lam Λ C wq r)) =
      atLogV D lam Λ C wq v (liftT D F) * ePh lam Λ C wq r := by
    rw [MvPowerSeries.subst_comp_subst_apply hSs hS's]
    have hid : (fun i => MvPowerSeries.subst S' (S i)) = MvPowerSeries.X := by
      funext i
      rw [hSi, subst_single_var S' hS's, hS'i, e.apply_symm_apply,
        ← PowerSeries.subst_comp_subst_apply hgs (PowerSeries.HasSubst.X i), hg,
        PowerSeries.subst_X (PowerSeries.HasSubst.X i)]
    rw [hid, MvPowerSeries.subst_self]
    rfl
  rw [← hback]
  exact integral_subst S' hS'0 (fun j => by rw [hS'i]; exact integral_subst_single_variable _ g gI) hSG

end Formalism.L2.KerInert
