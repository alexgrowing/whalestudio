import Mathlib
import Formalism.PeriodIntegrals.FglChordFactor
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalGroupChords.DerivativeFlog

noncomputable section

open Classical

namespace PI.FglChordFactor.Wk

open PI.AddIntG.Wk (SerS mem_SerS subst_psubst)

variable {p : ℕ} [Fact p.Prime]

def Pser (wq : PowerSeries ℂ_[p]) : MvPowerSeries (Fin 2) ℂ_[p] :=
  MvPowerSeries.X 0 ^ 2 * PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) wq -
    MvPowerSeries.X 1 ^ 2 * PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) wq

theorem cc_psubst {u : MvPowerSeries (Fin 2) ℂ_[p]} (hu : MvPowerSeries.constantCoeff u = 0)
    (g : PowerSeries ℂ_[p]) :
    MvPowerSeries.constantCoeff (PowerSeries.subst u g) = PowerSeries.constantCoeff g := by
  have hu' : PowerSeries.HasSubst u := PowerSeries.HasSubst.of_constantCoeff_zero hu
  rw [PowerSeries.constantCoeff_subst hu', finsum_eq_single _ 0]
  · simp
  · intro d hd
    simp [map_pow, hu, zero_pow hd]

theorem cc_msubst {φ : Fin 2 → MvPowerSeries (Fin 2) ℂ_[p]} (hφ : MvPowerSeries.HasSubst φ)
    (hφ0 : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0) (H : MvPowerSeries (Fin 2) ℂ_[p]) :
    MvPowerSeries.constantCoeff (MvPowerSeries.subst φ H) = MvPowerSeries.constantCoeff H := by
  rw [MvPowerSeries.constantCoeff_subst hφ, finsum_eq_single _ 0]
  · simp
  · intro d hd
    obtain ⟨s, hs⟩ : ∃ s, d s ≠ 0 := by
      by_contra h
      push_neg at h
      exact hd (Finsupp.ext h)
    have h0 : MvPowerSeries.constantCoeff (d.prod fun s e => φ s ^ e) = 0 := by
      rw [Finsupp.prod, map_prod]
      apply Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs)
      simp [hφ0, zero_pow hs]
    rw [h0, smul_zero]

theorem subst_pair_formal_add {l ex : PowerSeries ℂ_[p]} (hl0 : PowerSeries.constantCoeff l = 0)
    {u v : MvPowerSeries (Fin 2) ℂ_[p]} (hs : MvPowerSeries.HasSubst ![u, v]) :
    MvPowerSeries.subst ![u, v] (add l ex (MvPowerSeries.X 0) (MvPowerSeries.X 1)) = add l ex u v := by
  have hA : PowerSeries.HasSubst (PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) l +
      PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) l) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by
      rw [map_add, cc_psubst (MvPowerSeries.constantCoeff_X 0), cc_psubst (MvPowerSeries.constantCoeff_X 1),
        hl0, add_zero])
  unfold PI.FglChordFactor.add PI.FglChordFactor.pt PI.FglChordFactor.lg
  rw [subst_psubst hA hs, ← MvPowerSeries.coe_substAlgHom hs, map_add, MvPowerSeries.coe_substAlgHom,
    subst_pair_first_series hs, subst_pair_second_series hs]

theorem subst_bivariateSeries_difference_pair {l ex : PowerSeries ℂ_[p]} (hl0 : PowerSeries.constantCoeff l = 0)
    {u v : MvPowerSeries (Fin 2) ℂ_[p]} (hs : MvPowerSeries.HasSubst ![u, v]) :
    MvPowerSeries.subst ![u, v] (sub l ex (MvPowerSeries.X 0) (MvPowerSeries.X 1)) = sub l ex u v := by
  have hA : PowerSeries.HasSubst (PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) l -
      PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) l) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by
      rw [map_sub, cc_psubst (MvPowerSeries.constantCoeff_X 0), cc_psubst (MvPowerSeries.constantCoeff_X 1),
        hl0, sub_zero])
  unfold PI.FglChordFactor.sub PI.FglChordFactor.pt PI.FglChordFactor.lg
  rw [subst_psubst hA hs, ← MvPowerSeries.coe_substAlgHom hs, map_sub, MvPowerSeries.coe_substAlgHom,
    subst_pair_first_series hs, subst_pair_second_series hs]

theorem negsub {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]} (h : IsWq W wq)
    {u : MvPowerSeries (Fin 2) ℂ_[p]} (hu : PowerSeries.HasSubst u) :
    PowerSeries.subst (PowerSeries.subst u (iW W wq)) (flog W wq) = -PowerSeries.subst u (flog W wq) := by
  rw [← PowerSeries.subst_comp_subst_apply (hasSubst_iW W wq) hu, flog_iW h,
    ← PowerSeries.coe_substAlgHom hu, map_neg]

theorem mulD_at (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) {u : MvPowerSeries (Fin 2) ℂ_[p]}
    (hu : PowerSeries.HasSubst u) :
    PowerSeries.subst u (iW W wq) * PowerSeries.subst u (Dser W wq) = -u := by
  rw [← PowerSeries.coe_substAlgHom hu, ← map_mul, iW_mul_D, map_neg, PowerSeries.coe_substAlgHom,
    PowerSeries.subst_X hu]

theorem constantCoeff_inverse_variable (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) (i : Fin 2) :
    MvPowerSeries.constantCoeff (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) ℂ_[p]) (iW W wq)) = 0 := by
  rw [cc_psubst (MvPowerSeries.constantCoeff_X i) _, iW_const]

private theorem subst_zero_eq_zero_of_constantCoeff_zero {g : PowerSeries ℂ_[p]} (hg : PowerSeries.constantCoeff g = 0) :
    PowerSeries.subst (0 : MvPowerSeries (Fin 2) ℂ_[p]) g = 0 := by
  have h0 : PowerSeries.HasSubst (0 : MvPowerSeries (Fin 2) ℂ_[p]) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (map_zero _)
  obtain ⟨q, hq⟩ := PowerSeries.X_dvd_iff.mpr hg
  rw [hq, ← PowerSeries.coe_substAlgHom h0, map_mul, PowerSeries.coe_substAlgHom, PowerSeries.subst_X h0,
    zero_mul]

theorem F_at_ia {W : WeierstrassCurve ℂ_[p]} {wq ex : PowerSeries ℂ_[p]} (hW : IsWq W wq)
    (hex0 : PowerSeries.constantCoeff ex = 0) :
    MvPowerSeries.subst ![MvPowerSeries.X 0,
      PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) (iW W wq)]
      (add (flog W wq) ex (MvPowerSeries.X 0) (MvPowerSeries.X 1)) = 0 := by
  rw [subst_pair_formal_add (flog_const W wq) (hasSubst2 (MvPowerSeries.constantCoeff_X 0) (constantCoeff_inverse_variable W wq 0))]
  simp only [PI.FglChordFactor.add, PI.FglChordFactor.sub, PI.FglChordFactor.pt, PI.FglChordFactor.lg]
  rw [negsub hW (PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X 0 : MvPowerSeries.constantCoeff (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) = 0)), add_neg_cancel, subst_zero_eq_zero_of_constantCoeff_zero hex0]

theorem F'_at_aa {W : WeierstrassCurve ℂ_[p]} {wq ex : PowerSeries ℂ_[p]} (hex0 : PowerSeries.constantCoeff ex = 0) :
    MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]), MvPowerSeries.X 0]
      (sub (flog W wq) ex (MvPowerSeries.X 0) (MvPowerSeries.X 1)) = 0 := by
  rw [subst_bivariateSeries_difference_pair (flog_const W wq) (hasSubst2 (MvPowerSeries.constantCoeff_X 0) (MvPowerSeries.constantCoeff_X 0))]
  simp only [PI.FglChordFactor.add, PI.FglChordFactor.sub, PI.FglChordFactor.pt, PI.FglChordFactor.lg]
  rw [sub_self, subst_zero_eq_zero_of_constantCoeff_zero hex0]

theorem F'_eq {W : WeierstrassCurve ℂ_[p]} {wq ex : PowerSeries ℂ_[p]} (hW : IsWq W wq) :
    sub (flog W wq) ex (MvPowerSeries.X 0) (MvPowerSeries.X 1) =
      MvPowerSeries.subst ![MvPowerSeries.X 0,
        PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) (iW W wq)]
        (add (flog W wq) ex (MvPowerSeries.X 0) (MvPowerSeries.X 1)) := by
  rw [subst_pair_formal_add (flog_const W wq) (hasSubst2 (MvPowerSeries.constantCoeff_X 0) (constantCoeff_inverse_variable W wq 1))]
  simp only [PI.FglChordFactor.add, PI.FglChordFactor.sub, PI.FglChordFactor.pt, PI.FglChordFactor.lg]
  rw [negsub hW (PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X 1 : MvPowerSeries.constantCoeff (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) = 0)), sub_eq_add_neg]

theorem P_at_diagonal (wq : PowerSeries ℂ_[p]) :
    MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]), MvPowerSeries.X 0] (Pser wq) = 0 := by
  have hs := hasSubst2 (MvPowerSeries.constantCoeff_X 0 : MvPowerSeries.constantCoeff (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) = 0) (MvPowerSeries.constantCoeff_X 0)
  unfold Pser
  rw [← MvPowerSeries.coe_substAlgHom hs, map_sub, map_mul, map_mul, map_pow, map_pow,
    MvPowerSeries.coe_substAlgHom, subst_pair_first_variable hs, subst_pair_second_variable hs, subst_pair_first_series hs, subst_pair_second_series hs, sub_self]

theorem P_at_inverse {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]} (hW : IsWq W wq) :
    MvPowerSeries.subst ![MvPowerSeries.X 0,
      PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) (iW W wq)] (Pser wq) = 0 := by
  have hX0 : PowerSeries.HasSubst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) := PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X 0 : MvPowerSeries.constantCoeff (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) = 0)
  have hs := hasSubst2 (MvPowerSeries.constantCoeff_X 0) (constantCoeff_inverse_variable W wq 0)
  have hm := mulD_at W wq hX0
  have key : ∀ a i d w : MvPowerSeries (Fin 2) ℂ_[p], i * d = -a → a ^ 2 * w - i ^ 2 * (w * d ^ 2) = 0 := by
    intro a i d w h
    linear_combination (-(i * d - a) * w) * h
  unfold Pser
  rw [← MvPowerSeries.coe_substAlgHom hs, map_sub, map_mul, map_mul, map_pow, map_pow,
    MvPowerSeries.coe_substAlgHom, subst_pair_first_variable hs, subst_pair_second_variable hs, subst_pair_first_series hs, subst_pair_second_series hs,
    ← PowerSeries.subst_comp_subst_apply (hasSubst_iW W wq) hX0, wq_iW hW,
    ← PowerSeries.coe_substAlgHom hX0, map_mul, map_pow, PowerSeries.coe_substAlgHom]
  exact key _ _ _ _ hm

theorem formal_add_first_zero {W : WeierstrassCurve ℂ_[p]} {wq ex : PowerSeries ℂ_[p]}
    (hexl : PowerSeries.subst (flog W wq) ex = PowerSeries.X) :
    MvPowerSeries.subst ![(0 : MvPowerSeries (Fin 2) ℂ_[p]), MvPowerSeries.X 1]
      (add (flog W wq) ex (MvPowerSeries.X 0) (MvPowerSeries.X 1)) = MvPowerSeries.X 1 := by
  have hX1 : PowerSeries.HasSubst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) := PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X 1 : MvPowerSeries.constantCoeff (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) = 0)
  have hl : PowerSeries.HasSubst (flog W wq) := PowerSeries.HasSubst.of_constantCoeff_zero (flog_const W wq)
  rw [subst_pair_formal_add (flog_const W wq) (hasSubst2 (map_zero _) (MvPowerSeries.constantCoeff_X 1))]
  simp only [PI.FglChordFactor.add, PI.FglChordFactor.sub, PI.FglChordFactor.pt, PI.FglChordFactor.lg]
  rw [subst_zero_eq_zero_of_constantCoeff_zero (flog_const W wq), zero_add, ← PowerSeries.subst_comp_subst_apply hl hX1, hexl,
    PowerSeries.subst_X hX1]

theorem formal_sub_first_zero {W : WeierstrassCurve ℂ_[p]} {wq ex : PowerSeries ℂ_[p]} (hW : IsWq W wq)
    (hexl : PowerSeries.subst (flog W wq) ex = PowerSeries.X) :
    MvPowerSeries.subst ![(0 : MvPowerSeries (Fin 2) ℂ_[p]), MvPowerSeries.X 1]
      (sub (flog W wq) ex (MvPowerSeries.X 0) (MvPowerSeries.X 1)) =
      PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) (iW W wq) := by
  have hX1 : PowerSeries.HasSubst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) := PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X 1 : MvPowerSeries.constantCoeff (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) = 0)
  have hl : PowerSeries.HasSubst (flog W wq) := PowerSeries.HasSubst.of_constantCoeff_zero (flog_const W wq)
  have hi : PowerSeries.HasSubst (PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) (iW W wq)) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (constantCoeff_inverse_variable W wq 1)
  rw [subst_bivariateSeries_difference_pair (flog_const W wq) (hasSubst2 (map_zero _) (MvPowerSeries.constantCoeff_X 1))]
  simp only [PI.FglChordFactor.add, PI.FglChordFactor.sub, PI.FglChordFactor.pt, PI.FglChordFactor.lg]
  rw [subst_zero_eq_zero_of_constantCoeff_zero (flog_const W wq), zero_sub, ← negsub hW hX1, ← PowerSeries.subst_comp_subst_apply hl hi,
    hexl, PowerSeries.subst_X hi]

end PI.FglChordFactor.Wk
