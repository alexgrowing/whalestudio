import Mathlib
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.FinalA
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.StatementD

noncomputable section

namespace Formalism.L2.Th1.B.Fs

open Formalism.InvariantFactorPaths.G7 (at1)

section

variable {K : Type} [Field K] [CharZero K]

local notation "A3" => MvPowerSeries (Fin 3) K

theorem cc_psubst {ι : Type} {u : MvPowerSeries ι K} (hu : MvPowerSeries.constantCoeff u = 0)
    {f : PowerSeries K} (hf : PowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (PowerSeries.subst u f) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero hu _ hf

theorem psubst_fExp {ι : Type} {u : MvPowerSeries ι K} (hu : MvPowerSeries.constantCoeff u = 0)
    {f : PowerSeries K} (hf : PowerSeries.constantCoeff f = 0) :
    PowerSeries.subst u (fExp f) = fExp (PowerSeries.subst u f) :=
  Formalism.L2.Th1.B.subst_fExp (ι := Unit) (φ := fun _ => u) (fun _ => hu) hf

theorem sigS_cc (P : PowerSeries K) : PowerSeries.constantCoeff (sigS P) = 0 := Add0.sigS_cc P

theorem subst_sigma {ι : Type} (P : PowerSeries K) {u : MvPowerSeries ι K}
    (hu : MvPowerSeries.constantCoeff u = 0) :
    PowerSeries.subst u (sigma P) = u * fExp (PowerSeries.subst u (sigS P)) := by
  have hs := PowerSeries.HasSubst.of_constantCoeff_zero hu
  rw [sigma, PowerSeries.subst_mul hs, PowerSeries.subst_X hs, psubst_fExp hu (sigS_cc P)]

theorem subst_sgStar {ι : Type} (s2 : K) (P : PowerSeries K)
    {u : MvPowerSeries ι K} (hu : MvPowerSeries.constantCoeff u = 0) :
    PowerSeries.subst u (sgStar s2 P) =
      PowerSeries.subst u (sigma P) * fExp (-(MvPowerSeries.C (s2 / 2) * u ^ 2)) := by
  have hs := PowerSeries.HasSubst.of_constantCoeff_zero hu
  rw [sgStar, PowerSeries.subst_mul hs, psubst_fExp hu (by simp)]
  congr 2
  rw [← PowerSeries.coe_substAlgHom hs, map_neg, map_mul, map_pow, PowerSeries.substAlgHom_X,
    PowerSeries.coe_substAlgHom hs, PowerSeries.subst_C]

theorem pd_psubst (i : Fin 3) {u : A3} (hu : MvPowerSeries.constantCoeff u = 0)
    (f : PowerSeries K) : pd i (PowerSeries.subst u f) = PowerSeries.subst u (dz f) * pd i u :=
  Formalism.G.LogCR.pderiv_psubst hu f i

theorem hs_emb (j k : Fin 3) :
    MvPowerSeries.HasSubst ![(MvPowerSeries.X j : A3), MvPowerSeries.X k] :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero fun s => by fin_cases s <;> simp

def emb (j k : Fin 3) : MvPowerSeries (Fin 2) K →ₐ[K] A3 := MvPowerSeries.substAlgHom (hs_emb j k)

theorem emb_apply (j k : Fin 3) (h : MvPowerSeries (Fin 2) K) :
    emb j k h = MvPowerSeries.subst ![(MvPowerSeries.X j : A3), MvPowerSeries.X k] h := by
  rw [emb, MvPowerSeries.coe_substAlgHom]

theorem embed_pair_X_zero (j k : Fin 3) : emb (K := K) j k (MvPowerSeries.X 0) = MvPowerSeries.X j := by
  rw [emb, MvPowerSeries.substAlgHom_X]; rfl

theorem embed_pair_X_one (j k : Fin 3) : emb (K := K) j k (MvPowerSeries.X 1) = MvPowerSeries.X k := by
  rw [emb, MvPowerSeries.substAlgHom_X]; rfl

theorem emb_psubst (j k : Fin 3) (f : PowerSeries K) {u : MvPowerSeries (Fin 2) K}
    (hu : MvPowerSeries.constantCoeff u = 0) :
    emb j k (PowerSeries.subst u f) = PowerSeries.subst (emb j k u) f := by
  rw [emb_apply, emb_apply, psubst_msubst f hu (hs_emb j k)]

theorem embed_pair_at_variable_zero (j k : Fin 3) (f : PowerSeries K) : emb j k (at1 0 f) = at1 j f := by
  rw [at1, emb_psubst j k f (by simp), embed_pair_X_zero]; rfl

theorem embed_pair_at_variable_one (j k : Fin 3) (f : PowerSeries K) : emb j k (at1 1 f) = at1 k f := by
  rw [at1, emb_psubst j k f (by simp), embed_pair_X_one]; rfl

theorem emb_atD (j k : Fin 3) (f : PowerSeries K) : emb j k (atD f) = evalDiffThree j k f := by
  rw [atD, emb_psubst j k f (by simp), map_sub, embed_pair_X_zero, embed_pair_X_one]; rfl

theorem emb_atS (j k : Fin 3) (f : PowerSeries K) :
    emb j k (atS f) = PowerSeries.subst (MvPowerSeries.X j + MvPowerSeries.X k : A3) f := by
  rw [atS, emb_psubst j k f (by simp), map_add, embed_pair_X_zero, embed_pair_X_one]

theorem emb_wpDiff (j k : Fin 3) (P : PowerSeries K) : emb j k (wpDiff P) = wp3 P j k := by
  simp only [wpDiff, wp3, map_add, map_sub, map_mul, map_pow, embed_pair_X_zero, embed_pair_X_one, embed_pair_at_variable_zero,
    embed_pair_at_variable_one]

theorem emb_fExp (j k : Fin 3) {f : MvPowerSeries (Fin 2) K}
    (hf : MvPowerSeries.constantCoeff f = 0) : emb j k (fExp f) = fExp (emb j k f) := by
  rw [emb_apply, emb_apply]
  exact Formalism.L2.Th1.B.subst_fExp (fun s => by fin_cases s <;> simp) hf

theorem pd_emb_0 {j k : Fin 3} (hjk : j ≠ k) (h : MvPowerSeries (Fin 2) K) :
    pd j (emb j k h) = emb j k (pd 0 h) := by
  rw [emb_apply, emb_apply, pd,
    Formalism.G.LogCR.pderiv_subst (fun s => by fin_cases s <;> simp) h j, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [MvPowerSeries.pderiv_X_self, MvPowerSeries.pderiv_X_of_ne hjk.symm, mul_one, mul_zero,
    add_zero]

theorem pd_emb_1 {j k : Fin 3} (hjk : j ≠ k) (h : MvPowerSeries (Fin 2) K) :
    pd k (emb j k h) = emb j k (pd 1 h) := by
  rw [emb_apply, emb_apply, pd,
    Formalism.G.LogCR.pderiv_subst (fun s => by fin_cases s <;> simp) h k, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [MvPowerSeries.pderiv_X_self, MvPowerSeries.pderiv_X_of_ne hjk, mul_one, mul_zero,
    zero_add]

theorem tau3 (hT : TauRule) {g2 g3 : K} {P : PowerSeries K} (hP : IsWp g2 g3 P) {j k : Fin 3}
    (hjk : j ≠ k) :
    (MvPowerSeries.X j - MvPowerSeries.X k) * (pd j (wp3 P j k) - pd k (wp3 P j k)) =
      wp3 P j k * (2 + 2 * (MvPowerSeries.X j - MvPowerSeries.X k) *
        (evalDiffThree j k (dz (sigS P)) - at1 j (dz (sigS P)) + at1 k (dz (sigS P)))) := by
  have h := congrArg (emb j k) (hT K g2 g3 P hP)
  simp only [map_add, map_sub, map_mul, map_ofNat, embed_pair_X_zero, embed_pair_X_one, embed_pair_at_variable_zero, embed_pair_at_variable_one, emb_atD,
    emb_wpDiff, ← pd_emb_0 hjk, ← pd_emb_1 hjk] at h
  exact h

theorem wp3_apply_eq_sq_mul_sub_sq_mul {g2 g3 : K} {P : PowerSeries K} (hP : IsWp g2 g3 P) (j k : Fin 3) :
    wp3 P j k = (MvPowerSeries.X j ^ 2 - MvPowerSeries.X k ^ 2) *
      fExp (emb j k (par0 (sigS P))) := by
  have hN1 : MvPowerSeries.constantCoeff
      (1 - MvPowerSeries.X 0 ^ 2 * MvPowerSeries.X 1 ^ 2 * dq P : MvPowerSeries (Fin 2) K) = 1 := by
    simp
  have c0 : MvPowerSeries.constantCoeff (par0 (sigS P)) = 0 := by
    rw [addSigmaLog K g2 g3 P hP]; exact constantCoeff_fLog hN1
  rw [← emb_wpDiff, Add0.wpDiff_eq dqRule hP.2.1, ← fExp_fLog hN1, ← addSigmaLog K g2 g3 P hP,
    map_mul, emb_fExp j k c0, map_sub, map_pow, map_pow, embed_pair_X_zero, embed_pair_X_one]

theorem hasSubst_eval_last_zero :
    MvPowerSeries.HasSubst ![(MvPowerSeries.X 0 : A3), MvPowerSeries.X 1, 0] :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero fun s => by fin_cases s <;> simp

def ev3H : A3 →ₐ[K] A3 := MvPowerSeries.substAlgHom hasSubst_eval_last_zero

theorem eval_three_eq_eval_last_zero (h : A3) : ev3 h = ev3H h := by
  rw [ev3H, MvPowerSeries.coe_substAlgHom]; rfl

theorem eval_last_zero_X_zero : ev3H (K := K) (MvPowerSeries.X 0) = MvPowerSeries.X 0 := by
  rw [ev3H, MvPowerSeries.substAlgHom_X]; rfl

theorem eval_last_zero_X_one : ev3H (K := K) (MvPowerSeries.X 1) = MvPowerSeries.X 1 := by
  rw [ev3H, MvPowerSeries.substAlgHom_X]; rfl

theorem eval_last_zero_X_two : ev3H (K := K) (MvPowerSeries.X 2) = 0 := by
  rw [ev3H, MvPowerSeries.substAlgHom_X]; rfl

theorem eval_last_zero_subst_series (f : PowerSeries K) {u : A3} (hu : MvPowerSeries.constantCoeff u = 0) :
    ev3H (PowerSeries.subst u f) = PowerSeries.subst (ev3H u) f := by
  rw [← eval_three_eq_eval_last_zero, ← eval_three_eq_eval_last_zero, ev3, ev3, psubst_msubst f hu hasSubst_eval_last_zero]

theorem eval_last_zero_formal_exp {f : A3} (hf : MvPowerSeries.constantCoeff f = 0) :
    ev3H (fExp f) = fExp (ev3H f) := by
  rw [← eval_three_eq_eval_last_zero, ← eval_three_eq_eval_last_zero]
  exact Formalism.L2.Th1.B.subst_fExp (fun s => by fin_cases s <;> simp) hf

theorem eval_last_zero_at_variable_zero (f : PowerSeries K) : ev3H (at1 0 f) = at1 0 f := by
  rw [at1, eval_last_zero_subst_series f (by simp), eval_last_zero_X_zero]

theorem eval_last_zero_at_variable_one (f : PowerSeries K) : ev3H (at1 1 f) = at1 1 f := by
  rw [at1, eval_last_zero_subst_series f (by simp), eval_last_zero_X_one]

theorem det_three_points_eq_expansion (P : PowerSeries K) : det3 P =
    MvPowerSeries.X 0 ^ 3 * (MvPowerSeries.X 1 * (1 + MvPowerSeries.X 1 ^ 2 * at1 1 P)) *
        (-2 + MvPowerSeries.X 2 ^ 3 * at1 2 (dz P)) -
      MvPowerSeries.X 0 ^ 3 * (-2 + MvPowerSeries.X 1 ^ 3 * at1 1 (dz P)) *
        (MvPowerSeries.X 2 * (1 + MvPowerSeries.X 2 ^ 2 * at1 2 P)) -
      MvPowerSeries.X 0 * (1 + MvPowerSeries.X 0 ^ 2 * at1 0 P) * MvPowerSeries.X 1 ^ 3 *
        (-2 + MvPowerSeries.X 2 ^ 3 * at1 2 (dz P)) +
      MvPowerSeries.X 0 * (1 + MvPowerSeries.X 0 ^ 2 * at1 0 P) *
        (-2 + MvPowerSeries.X 1 ^ 3 * at1 1 (dz P)) * MvPowerSeries.X 2 ^ 3 +
      (-2 + MvPowerSeries.X 0 ^ 3 * at1 0 (dz P)) * MvPowerSeries.X 1 ^ 3 *
        (MvPowerSeries.X 2 * (1 + MvPowerSeries.X 2 ^ 2 * at1 2 P)) -
      (-2 + MvPowerSeries.X 0 ^ 3 * at1 0 (dz P)) *
        (MvPowerSeries.X 1 * (1 + MvPowerSeries.X 1 ^ 2 * at1 1 P)) * MvPowerSeries.X 2 ^ 3 := by
  rw [det3, Matrix.det_fin_three]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]

theorem eval_last_zero_det_three_points (P : PowerSeries K) :
    ev3H (det3 P) = -2 * (MvPowerSeries.X 0 * MvPowerSeries.X 1) * wp3 P 0 1 := by
  rw [det_three_points_eq_expansion]
  simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_one, map_ofNat, eval_last_zero_X_zero, eval_last_zero_X_one,
    eval_last_zero_X_two, eval_last_zero_at_variable_zero, eval_last_zero_at_variable_one, wp3]
  ring

theorem eval_last_zero_vandermonde_three : ev3H (vand3 K) =
    (MvPowerSeries.X 0 * MvPowerSeries.X 1) * (MvPowerSeries.X 0 ^ 2 - MvPowerSeries.X 1 ^ 2) := by
  simp only [vand3, map_add, map_sub, map_mul, eval_last_zero_X_zero, eval_last_zero_X_one, eval_last_zero_X_two]
  ring

theorem eval_last_zero_exp_parallelogram {f : PowerSeries K} (hf : PowerSeries.constantCoeff f = 0) :
    ev3H (fsE f) = emb 0 1 (par0 f) := by
  have h0 : PowerSeries.subst (0 : A3) f = 0 := PowerSeries.subst_zero_of_constantCoeff_zero hf
  simp only [fsE, par0, evalSumThree, evalDiffThree, map_add, map_sub, map_mul, map_ofNat, emb_atS, emb_atD,
    embed_pair_at_variable_zero, embed_pair_at_variable_one]
  rw [eval_last_zero_subst_series f (by simp), eval_last_zero_subst_series f (by simp), eval_last_zero_subst_series f (by simp),
    eval_last_zero_subst_series f (by simp), eval_last_zero_at_variable_zero, eval_last_zero_at_variable_one, at1, at1, at1, eval_last_zero_subst_series f (by simp)]
  simp only [map_add, map_sub, eval_last_zero_X_zero, eval_last_zero_X_one, eval_last_zero_X_two, add_zero, sub_zero, h0]
  ring

theorem fsE_cc {f : PowerSeries K} (hf : PowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (fsE f) = 0 := by
  simp only [fsE, evalSumThree, evalDiffThree, at1, map_add, map_sub, map_mul]
  rw [cc_psubst (by simp) hf, cc_psubst (by simp) hf, cc_psubst (by simp) hf,
    cc_psubst (by simp) hf, cc_psubst (by simp) hf, cc_psubst (by simp) hf,
    cc_psubst (by simp) hf]
  simp

theorem ne_zero_of_pd {f : A3} (i : Fin 3) (h : pd i f = 1) : f ≠ 0 := by
  rintro rfl
  simp at h

theorem X_ne_zero (j : Fin 3) : (MvPowerSeries.X j : A3) ≠ 0 :=
  ne_zero_of_pd j MvPowerSeries.pderiv_X_self

theorem X_sub_ne_zero {j k : Fin 3} (hjk : j ≠ k) :
    (MvPowerSeries.X j - MvPowerSeries.X k : A3) ≠ 0 :=
  ne_zero_of_pd j (by
    rw [pd, map_sub, MvPowerSeries.pderiv_X_self, MvPowerSeries.pderiv_X_of_ne hjk.symm, sub_zero])

theorem X_add_ne_zero {j k : Fin 3} (hjk : j ≠ k) :
    (MvPowerSeries.X j + MvPowerSeries.X k : A3) ≠ 0 :=
  ne_zero_of_pd j (by
    rw [pd, map_add, MvPowerSeries.pderiv_X_self, MvPowerSeries.pderiv_X_of_ne hjk.symm, add_zero])

theorem sq_sub_ne_zero {j k : Fin 3} (hjk : j ≠ k) :
    (MvPowerSeries.X j ^ 2 - MvPowerSeries.X k ^ 2 : A3) ≠ 0 := by
  rw [sq_sub_sq]
  exact mul_ne_zero (X_add_ne_zero hjk) (X_sub_ne_zero hjk)

theorem fExp_ne_zero {f : A3} (hf : MvPowerSeries.constantCoeff f = 0) : fExp f ≠ 0 := by
  intro h
  have := constantCoeff_fExp hf
  rw [h] at this
  simp at this

theorem constantCoeff_parallelogram_defect {f : PowerSeries K} (hf : PowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (par0 f) = 0 := by
  simp only [par0, atS, atD, at1, map_add, map_sub, map_mul]
  rw [cc_psubst (by simp) hf, cc_psubst (by simp) hf, cc_psubst (by simp) hf,
    cc_psubst (by simp) hf]
  simp

theorem emb_cc (j k : Fin 3) {h : MvPowerSeries (Fin 2) K}
    (hh : MvPowerSeries.constantCoeff h = 0) : MvPowerSeries.constantCoeff (emb j k h) = 0 := by
  rw [emb_apply]
  exact MvPowerSeries.constantCoeff_subst_eq_zero (hs_emb j k)
    (fun s => by fin_cases s <;> simp) hh

theorem weierstrass_pair_ne_zero {g2 g3 : K} {P : PowerSeries K} (hP : IsWp g2 g3 P) {j k : Fin 3}
    (hjk : j ≠ k) : wp3 P j k ≠ 0 := by
  rw [wp3_apply_eq_sq_mul_sub_sq_mul hP]
  exact mul_ne_zero (sq_sub_ne_zero hjk) (fExp_ne_zero (emb_cc j k (constantCoeff_parallelogram_defect (sigS_cc P))))

theorem pdX (i j : Fin 3) :
    MvPowerSeries.pderiv K i (MvPowerSeries.X j : A3) = if j = i then 1 else 0 := by
  split_ifs with h
  · rw [h, MvPowerSeries.pderiv_X_self]
  · rw [MvPowerSeries.pderiv_X_of_ne h]

theorem pd_two (i : Fin 3) : MvPowerSeries.pderiv K i (2 : A3) = 0 := by
  simpa using (MvPowerSeries.pderiv K i).map_natCast 2

theorem pd_three (i : Fin 3) : MvPowerSeries.pderiv K i (3 : A3) = 0 := by
  simpa using (MvPowerSeries.pderiv K i).map_natCast 3

theorem pderiv_series_at_variable (i j : Fin 3) (f : PowerSeries K) :
    MvPowerSeries.pderiv K i (at1 j f : A3) = at1 j (dz f) * if j = i then 1 else 0 := by
  rw [← pdX]; exact pd_psubst i (by simp) f

theorem pderiv_series_at_difference_three (i j k : Fin 3) (f : PowerSeries K) :
    MvPowerSeries.pderiv K i (evalDiffThree j k f : A3) =
      evalDiffThree j k (dz f) * ((if j = i then 1 else 0) - if k = i then 1 else 0) := by
  rw [← pdX, ← pdX, ← map_sub]; exact pd_psubst i (by simp) f

theorem pderiv_series_at_sum_three (i : Fin 3) (f : PowerSeries K) :
    MvPowerSeries.pderiv K i (evalSumThree f : A3) = evalSumThree (dz f) := by
  have h := pd_psubst i (u := MvPowerSeries.X 0 + MvPowerSeries.X 1 + MvPowerSeries.X 2)
    (by simp) f
  simp only [pd, map_add, pdX] at h
  rw [evalSumThree, h]
  fin_cases i <;> simp [evalSumThree]

theorem D_vand3 : pd 1 (vand3 K) - pd 2 (vand3 K) =
    (MvPowerSeries.X 0 + MvPowerSeries.X 1 + MvPowerSeries.X 2) *
      (-((MvPowerSeries.X 0 - MvPowerSeries.X 2) * (MvPowerSeries.X 1 - MvPowerSeries.X 2)) +
        (MvPowerSeries.X 0 - MvPowerSeries.X 1) * (MvPowerSeries.X 1 - MvPowerSeries.X 2) +
        2 * ((MvPowerSeries.X 0 - MvPowerSeries.X 1) * (MvPowerSeries.X 0 - MvPowerSeries.X 2))) := by
  simp only [vand3, pd, Derivation.leibniz, map_add, map_sub, smul_eq_mul, pdX]
  simp
  ring

theorem D_fsE (f : PowerSeries K) : pd 1 (fsE f) - pd 2 (fsE f) =
    -(evalDiffThree 0 1 (dz f) - at1 0 (dz f) + at1 1 (dz f)) +
      (evalDiffThree 0 2 (dz f) - at1 0 (dz f) + at1 2 (dz f)) +
      2 * (evalDiffThree 1 2 (dz f) - at1 1 (dz f) + at1 2 (dz f)) := by
  simp only [fsE, pd, Derivation.leibniz, map_add, map_sub, smul_eq_mul, pd_three, pderiv_series_at_variable, pderiv_series_at_difference_three,
    pderiv_series_at_sum_three]
  simp
  ring

theorem ring_core {R : Type} [CommRing R] (a b c M01 M02 M12 D01 D02 D12 t01 t02 t12 A DA : R)
    (T01 : (a - b) * D01 = M01 * (2 + 2 * (a - b) * t01))
    (T02 : (a - c) * D02 = M02 * (2 + 2 * (a - c) * t02))
    (T12 : (b - c) * D12 = M12 * (2 + 2 * (b - c) * t12))
    (hR : 2 * M01 * M02 * M12 * DA =
      A * (-D01 * M02 * M12 + D02 * M01 * M12 + 2 * D12 * M01 * M02)) :
    (2 * M01 * M02 * M12) *
        (A * ((a + b + c) * (-((a - c) * (b - c)) + (a - b) * (b - c) + 2 * ((a - b) * (a - c))) +
          (a + b + c) * (a - b) * (a - c) * (b - c) * (-t01 + t02 + 2 * t12))) =
      (2 * M01 * M02 * M12) * ((a + b + c) * (a - b) * (a - c) * (b - c) * DA) := by
  linear_combination (-((a + b + c) * (a - b) * (a - c) * (b - c))) * hR +
    A * M02 * M12 * (a + b + c) * (a - c) * (b - c) * T01 -
    A * M01 * M12 * (a + b + c) * (a - b) * (b - c) * T02 -
    2 * A * M01 * M02 * (a + b + c) * (a - b) * (a - c) * T12

end

theorem FrobStickLog_of (hS : ShearLemma) (hT : TauRule) (hD : DetRule) : FrobStickLog := by
  intro K _ _ g2 g3 P hP
  have cE : MvPowerSeries.constantCoeff (fsE (sigS P)) = 0 := fsE_cc (sigS_cc P)
  have two_ne : (2 : MvPowerSeries (Fin 3) K) ≠ 0 := by
    intro h
    have := congrArg MvPowerSeries.constantCoeff h
    rw [map_ofNat, map_zero] at this
    exact two_ne_zero this
  have hb : ev3H (-2 * vand3 K * fExp (fsE (sigS P))) =
      -2 * (MvPowerSeries.X 0 * MvPowerSeries.X 1) * wp3 P 0 1 := by
    rw [map_mul, map_mul, map_neg, map_ofNat, eval_last_zero_vandermonde_three, eval_last_zero_formal_exp cE, eval_last_zero_exp_parallelogram (sigS_cc P),
      wp3_apply_eq_sq_mul_sub_sq_mul hP]
    ring
  refine hS K _ _ ?_ ?_ ?_
  · have hY : ∀ i : Fin 3, pd i (-2 * vand3 K * fExp (fsE (sigS P))) =
        -2 * (pd i (vand3 K) * fExp (fsE (sigS P)) +
          vand3 K * (fExp (fsE (sigS P)) * pd i (fsE (sigS P)))) := by
      intro i
      have h1 := pd_fExp i cE
      simp only [pd] at h1 ⊢
      rw [Derivation.leibniz, Derivation.leibniz, h1, map_neg, pd_two]
      simp only [smul_eq_mul]
      ring
    have core := ring_core (MvPowerSeries.X 0) (MvPowerSeries.X 1) (MvPowerSeries.X 2) _ _ _ _ _ _
      _ _ _ _ _ (tau3 hT hP (j := 0) (k := 1) (by decide)) (tau3 hT hP (j := 0) (k := 2) (by decide))
      (tau3 hT hP (j := 1) (k := 2) (by decide)) (hD K g2 g3 P hP)
    have hM : 2 * wp3 P 0 1 * wp3 P 0 2 * wp3 P 1 2 ≠ 0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne (weierstrass_pair_ne_zero hP (by decide)))
        (weierstrass_pair_ne_zero hP (by decide))) (weierstrass_pair_ne_zero hP (by decide))
    have core' := mul_left_cancel₀ hM core
    have hV : vand3 K = (MvPowerSeries.X 0 + MvPowerSeries.X 1 + MvPowerSeries.X 2) *
      (MvPowerSeries.X 0 - MvPowerSeries.X 1) * (MvPowerSeries.X 0 - MvPowerSeries.X 2) *
      (MvPowerSeries.X 1 - MvPowerSeries.X 2) := rfl
    rw [← hV] at core'
    rw [hY, hY]
    linear_combination (-2 * fExp (fsE (sigS P))) * core' +
      (-2 * det3 P * fExp (fsE (sigS P))) * D_vand3 (K := K) +
      (-2 * det3 P * fExp (fsE (sigS P)) * vand3 K) * D_fsE (sigS P)
  · rw [eval_three_eq_eval_last_zero, eval_three_eq_eval_last_zero, hb, eval_last_zero_det_three_points]
  · rw [eval_three_eq_eval_last_zero, hb]
    exact mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr two_ne)
      (mul_ne_zero (X_ne_zero 0) (X_ne_zero 1))) (weierstrass_pair_ne_zero hP (by decide))

theorem fExp_three {K : Type} [Field K] [CharZero K] {ι : Type} {f : MvPowerSeries ι K}
    (hf : MvPowerSeries.constantCoeff f = 0) : fExp f ^ 3 = fExp (3 * f) := by
  have h3 : 3 * f = f + f + f := by ring
  rw [h3, fExp_add (by rw [map_add, hf, add_zero]) hf, fExp_add hf hf]
  ring

theorem FrobStick_of (hL : FrobStickLog) : FrobStick := by
  intro K _ _ g2 g3 P hP
  have h := hL K g2 g3 P hP
  have c0 : ∀ x : Fin 3, MvPowerSeries.constantCoeff
      (at1 x (sigS P) : MvPowerSeries (Fin 3) K) = 0 := fun x => cc_psubst (by simp) (sigS_cc P)
  have c3 : ∀ x : Fin 3, MvPowerSeries.constantCoeff
      (3 * at1 x (sigS P) : MvPowerSeries (Fin 3) K) = 0 := fun x => by rw [map_mul, c0, mul_zero]
  have cS : MvPowerSeries.constantCoeff (evalSumThree (sigS P)) = 0 := cc_psubst (by simp) (sigS_cc P)
  have cD : ∀ j k : Fin 3, MvPowerSeries.constantCoeff (evalDiffThree j k (sigS P)) = 0 :=
    fun j k => cc_psubst (by simp) (sigS_cc P)
  have cE : MvPowerSeries.constantCoeff (fsE (sigS P)) = 0 := fsE_cc (sigS_cc P)
  have key : fExp (at1 0 (sigS P)) ^ 3 * fExp (at1 1 (sigS P)) ^ 3 * fExp (at1 2 (sigS P)) ^ 3 *
        fExp (fsE (sigS P)) =
      fExp (evalSumThree (sigS P)) * fExp (evalDiffThree 0 1 (sigS P)) * fExp (evalDiffThree 0 2 (sigS P)) *
        fExp (evalDiffThree 1 2 (sigS P)) := by
    rw [fExp_three (c0 0), fExp_three (c0 1), fExp_three (c0 2), ← fExp_add (c3 0) (c3 1),
      ← fExp_add (by rw [map_add, c3, c3, add_zero]) (c3 2),
      ← fExp_add (by rw [map_add, map_add, c3, c3, c3, add_zero, add_zero]) cE,
      ← fExp_add cS (cD 0 1), ← fExp_add (by rw [map_add, cS, cD, add_zero]) (cD 0 2),
      ← fExp_add (by rw [map_add, map_add, cS, cD, cD, add_zero, add_zero]) (cD 1 2)]
    congr 1
    rw [fsE]
    ring
  have eS : evalSumThree (sigma P) = (MvPowerSeries.X 0 + MvPowerSeries.X 1 + MvPowerSeries.X 2) *
      fExp (evalSumThree (sigS P)) := subst_sigma P (by simp)
  have eD : ∀ j k : Fin 3, evalDiffThree j k (sigma P) = (MvPowerSeries.X j - MvPowerSeries.X k) *
      fExp (evalDiffThree j k (sigS P)) := fun j k => subst_sigma P (by simp)
  have e0 : ∀ x : Fin 3, (at1 x (sigma P) : MvPowerSeries (Fin 3) K) =
      MvPowerSeries.X x * fExp (at1 x (sigS P)) := fun x => subst_sigma P (by simp)
  rw [eS, eD, eD, eD, e0, e0, e0, h, vand3]
  linear_combination
    (-2 * (MvPowerSeries.X 0 * MvPowerSeries.X 1 * MvPowerSeries.X 2) ^ 3 *
      ((MvPowerSeries.X 0 + MvPowerSeries.X 1 + MvPowerSeries.X 2) *
        (MvPowerSeries.X 0 - MvPowerSeries.X 1) * (MvPowerSeries.X 0 - MvPowerSeries.X 2) *
        (MvPowerSeries.X 1 - MvPowerSeries.X 2))) * key

theorem FrobStickStar_of (hF : FrobStick) : FrobStickStar := by
  intro K _ _ g2 g3 s2 P hP
  have h := hF K g2 g3 P hP
  have cc : ∀ u : MvPowerSeries (Fin 3) K, MvPowerSeries.constantCoeff u = 0 →
      MvPowerSeries.constantCoeff (-(MvPowerSeries.C (s2 / 2) * u ^ 2)) = 0 := by
    intro u hu; simp [hu]
  have z : ∀ x : Fin 3, MvPowerSeries.constantCoeff
      (-(MvPowerSeries.C (s2 / 2) * (MvPowerSeries.X x : MvPowerSeries (Fin 3) K) ^ 2)) = 0 :=
    fun x => cc _ (by simp)
  have z3 : ∀ x : Fin 3, MvPowerSeries.constantCoeff
      (3 * -(MvPowerSeries.C (s2 / 2) * (MvPowerSeries.X x : MvPowerSeries (Fin 3) K) ^ 2)) = 0 :=
    fun x => by rw [map_mul, z, mul_zero]
  have zS := cc (MvPowerSeries.X 0 + MvPowerSeries.X 1 + MvPowerSeries.X 2) (by simp)
  have zD : ∀ j k : Fin 3, MvPowerSeries.constantCoeff
      (-(MvPowerSeries.C (s2 / 2) *
        (MvPowerSeries.X j - MvPowerSeries.X k : MvPowerSeries (Fin 3) K) ^ 2)) = 0 :=
    fun j k => cc _ (by simp)
  have key : (fExp (-(MvPowerSeries.C (s2 / 2) *
          (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K) ^ 2)) *
        fExp (-(MvPowerSeries.C (s2 / 2) * MvPowerSeries.X 1 ^ 2)) *
        fExp (-(MvPowerSeries.C (s2 / 2) * MvPowerSeries.X 2 ^ 2))) ^ 3 =
      fExp (-(MvPowerSeries.C (s2 / 2) *
          (MvPowerSeries.X 0 + MvPowerSeries.X 1 + MvPowerSeries.X 2) ^ 2)) *
        fExp (-(MvPowerSeries.C (s2 / 2) * (MvPowerSeries.X 0 - MvPowerSeries.X 1) ^ 2)) *
        fExp (-(MvPowerSeries.C (s2 / 2) * (MvPowerSeries.X 0 - MvPowerSeries.X 2) ^ 2)) *
        fExp (-(MvPowerSeries.C (s2 / 2) * (MvPowerSeries.X 1 - MvPowerSeries.X 2) ^ 2)) := by
    rw [mul_pow, mul_pow, fExp_three (z 0), fExp_three (z 1), fExp_three (z 2),
      ← fExp_add (z3 0) (z3 1), ← fExp_add (by rw [map_add, z3, z3, add_zero]) (z3 2),
      ← fExp_add zS (zD 0 1), ← fExp_add (by rw [map_add, zS, zD, add_zero]) (zD 0 2),
      ← fExp_add (by rw [map_add, map_add, zS, zD, zD, add_zero, add_zero]) (zD 1 2)]
    congr 1
    ring
  have eS : evalSumThree (sgStar s2 P) = evalSumThree (sigma P) * _ := subst_sgStar s2 P (by simp)
  have eD : ∀ j k : Fin 3, evalDiffThree j k (sgStar s2 P) = evalDiffThree j k (sigma P) * _ :=
    fun j k => subst_sgStar s2 P (by simp)
  have e0 : ∀ x : Fin 3, (at1 x (sgStar s2 P) : MvPowerSeries (Fin 3) K) = at1 x (sigma P) * _ :=
    fun x => subst_sgStar s2 P (by simp)
  rw [eS, eD, eD, eD, e0, e0, e0]
  linear_combination
    ((fExp (-(MvPowerSeries.C (s2 / 2) * (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K) ^ 2)) *
        fExp (-(MvPowerSeries.C (s2 / 2) * MvPowerSeries.X 1 ^ 2)) *
        fExp (-(MvPowerSeries.C (s2 / 2) * MvPowerSeries.X 2 ^ 2))) ^ 3) * h +
    (-2 * (MvPowerSeries.X 0 * MvPowerSeries.X 1 * MvPowerSeries.X 2) ^ 3 *
      (evalSumThree (sigma P) * evalDiffThree 0 1 (sigma P) * evalDiffThree 0 2 (sigma P) * evalDiffThree 1 2 (sigma P))) * key

end Formalism.L2.Th1.B.Fs
