import Mathlib
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.StatementB
import Formalism.FormalGroupLog.FormalGroupLogProofs.ConstantCoeffSubstOfZero
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.LogarithmEquivalence

noncomputable section

namespace Formalism.L2.Th1.B

open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob d1 in3 swap2 DivAB equivalence_rules)
open Formalism.G.LogP (hs2 subst2_subst psubst_subst psubst_injective subst_zero')

section Alg

variable {K : Type} [Field K] [CharZero K] {ι : Type}

theorem subst_at_variable_one_eq (f : PowerSeries K) (x : Fin 2) {b : Fin 2 → MvPowerSeries ι K}
    (hb : MvPowerSeries.HasSubst b) :
    MvPowerSeries.subst b (at1 x f) = PowerSeries.subst (b x) f := by
  unfold at1
  rw [psubst_subst f (by simp) hb, MvPowerSeries.subst_X hb]

theorem constantCoeff_subst_two_variables (F : MvPowerSeries (Fin 2) K) (hF : MvPowerSeries.constantCoeff F = 0)
    (U V : MvPowerSeries ι K) (hU : MvPowerSeries.constantCoeff U = 0)
    (hV : MvPowerSeries.constantCoeff V = 0) :
    MvPowerSeries.constantCoeff (MvPowerSeries.subst ![U, V] F) = 0 :=
  MvPowerSeries.constantCoeff_subst_eq_zero (hs2 hU hV)
    (fun i => by fin_cases i <;> simpa) hF

theorem constantCoeff_subst_one_variable (g : PowerSeries K) (hg : PowerSeries.constantCoeff g = 0)
    (U : MvPowerSeries ι K) (hU : MvPowerSeries.constantCoeff U = 0) :
    MvPowerSeries.constantCoeff (PowerSeries.subst U g) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero hU g hg

theorem cube_cob_subst (F : MvPowerSeries (Fin 2) K) (hF : MvPowerSeries.constantCoeff F = 0)
    (f : PowerSeries K) (U V : MvPowerSeries ι K) (hU : MvPowerSeries.constantCoeff U = 0)
    (hV : MvPowerSeries.constantCoeff V = 0) :
    MvPowerSeries.subst ![U, V] (cob F f) =
      PowerSeries.subst (MvPowerSeries.subst ![U, V] F) f - PowerSeries.subst U f -
        PowerSeries.subst V f := by
  have hb := hs2 hU hV
  unfold cob
  rw [← MvPowerSeries.coe_substAlgHom hb, map_sub, map_sub, MvPowerSeries.coe_substAlgHom hb,
    psubst_subst f hF hb, subst_at_variable_one_eq f 0 hb, subst_at_variable_one_eq f 1 hb]
  rfl

theorem cube_par_subst (F : MvPowerSeries (Fin 2) K) (hF : MvPowerSeries.constantCoeff F = 0)
    (i f : PowerSeries K) (hi : PowerSeries.constantCoeff i = 0) (U V : MvPowerSeries ι K)
    (hU : MvPowerSeries.constantCoeff U = 0) (hV : MvPowerSeries.constantCoeff V = 0) :
    MvPowerSeries.subst ![U, V] (par F i f) =
      PowerSeries.subst (MvPowerSeries.subst ![U, V] F) f +
        PowerSeries.subst (MvPowerSeries.subst ![U, PowerSeries.subst V i] F) f -
        2 * PowerSeries.subst U f - 2 * PowerSeries.subst V f := by
  have hb := hs2 hU hV
  have h1 : MvPowerSeries.constantCoeff (at1 (1 : Fin 2) i) = 0 := constantCoeff_subst_one_variable i hi _ (by simp)
  have hFI : MvPowerSeries.constantCoeff (FI F i) = 0 := constantCoeff_subst_two_variables F hF _ _ (by simp) h1
  unfold par
  rw [← MvPowerSeries.coe_substAlgHom hb, map_sub, map_sub, map_add, map_mul, map_mul, map_ofNat,
    MvPowerSeries.coe_substAlgHom hb, psubst_subst f hF hb, psubst_subst f hFI hb,
    subst_at_variable_one_eq f 0 hb, subst_at_variable_one_eq f 1 hb]
  unfold FI
  rw [subst2_subst F (by simp) h1 hb, MvPowerSeries.subst_X hb, subst_at_variable_one_eq i 1 hb]
  rfl

theorem two_mul_C_inv_two : (2 : MvPowerSeries ι K) * MvPowerSeries.C (2 : K)⁻¹ = 1 := by
  have e : (2 : MvPowerSeries ι K) = MvPowerSeries.C (2 : K) := (map_ofNat MvPowerSeries.C 2).symm
  rw [e, ← map_mul, mul_inv_cancel₀ two_ne_zero, map_one]

end Alg

section Norm

variable {K : Type} [NormedField K] [CharZero K] {ι : Type}

theorem cube_log_add {F : MvPowerSeries (Fin 2) K} {l : PowerSeries K} (h : LawLog F l)
    (U V : MvPowerSeries ι K) (hU : MvPowerSeries.constantCoeff U = 0)
    (hV : MvPowerSeries.constantCoeff V = 0) :
    PowerSeries.subst (MvPowerSeries.subst ![U, V] F) l =
      PowerSeries.subst U l + PowerSeries.subst V l := by
  obtain ⟨hF, -, -, -, hc⟩ := h
  have e := cube_cob_subst F hF l U V hU hV
  rw [hc, subst_zero' (hs2 hU hV)] at e
  linear_combination -e

theorem cube_log_inv {l i : PowerSeries K} (hi : IsInv l i) (V : MvPowerSeries ι K)
    (hV : MvPowerSeries.constantCoeff V = 0) :
    PowerSeries.subst (PowerSeries.subst V i) l = -PowerSeries.subst V l := by
  have hVs : PowerSeries.HasSubst V := PowerSeries.HasSubst.of_constantCoeff_zero hV
  rw [← PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hi.1) hVs,
    hi.2.2, ← PowerSeries.coe_substAlgHom hVs, map_neg]

theorem cube_log_half {l hf : PowerSeries K} (hh : IsHalf l hf) (V : MvPowerSeries ι K)
    (hV : MvPowerSeries.constantCoeff V = 0) :
    2 * PowerSeries.subst (PowerSeries.subst V hf) l = PowerSeries.subst V l := by
  have hVs : PowerSeries.HasSubst V := PowerSeries.HasSubst.of_constantCoeff_zero hV
  rw [← PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hh.1) hVs,
    hh.2.2, PowerSeries.subst_mul hVs, PowerSeries.subst_C, ← mul_assoc, two_mul_C_inv_two, one_mul]

theorem cube_add_eq {F : MvPowerSeries (Fin 2) K} {l : PowerSeries K} (h : LawLog F l)
    (U V W : MvPowerSeries ι K) (hU : MvPowerSeries.constantCoeff U = 0)
    (hV : MvPowerSeries.constantCoeff V = 0) (hW : MvPowerSeries.constantCoeff W = 0)
    (e : PowerSeries.subst U l + PowerSeries.subst V l = PowerSeries.subst W l) :
    MvPowerSeries.subst ![U, V] F = W :=
  psubst_injective h.2.2.1 h.2.2.2.1 (constantCoeff_subst_two_variables F h.1 U V hU hV) hW
    ((cube_log_add h U V hU hV).trans e)

theorem cube_sub_eq {F : MvPowerSeries (Fin 2) K} {l i : PowerSeries K} (h : LawLog F l)
    (hi : IsInv l i) (U V W : MvPowerSeries ι K) (hU : MvPowerSeries.constantCoeff U = 0)
    (hV : MvPowerSeries.constantCoeff V = 0) (hW : MvPowerSeries.constantCoeff W = 0)
    (e : PowerSeries.subst U l - PowerSeries.subst V l = PowerSeries.subst W l) :
    MvPowerSeries.subst ![U, PowerSeries.subst V i] F = W :=
  cube_add_eq h U _ W hU (constantCoeff_subst_one_variable i hi.1 V hV) hW (by rw [cube_log_inv hi V hV, ← e]; ring)

theorem cube_identity {F : MvPowerSeries (Fin 2) K} {l i : PowerSeries K} (h : LawLog F l)
    (hi : IsInv l i) (f : PowerSeries K) (hf0 : PowerSeries.constantCoeff f = 0)
    (x0 x1 x2 A B C : MvPowerSeries ι K)
    (h0 : MvPowerSeries.constantCoeff x0 = 0) (h1 : MvPowerSeries.constantCoeff x1 = 0)
    (h2 : MvPowerSeries.constantCoeff x2 = 0) (hA : MvPowerSeries.constantCoeff A = 0)
    (hB : MvPowerSeries.constantCoeff B = 0) (hC : MvPowerSeries.constantCoeff C = 0)
    (eA : PowerSeries.subst A l = PowerSeries.subst x0 l + PowerSeries.subst B l)
    (eB : 2 * PowerSeries.subst B l = PowerSeries.subst x1 l + PowerSeries.subst x2 l)
    (eC : 2 * PowerSeries.subst C l = PowerSeries.subst x1 l - PowerSeries.subst x2 l) :
    MvPowerSeries.subst ![A, B] (par F i f) - MvPowerSeries.subst ![A, C] (par F i f) +
        MvPowerSeries.subst ![B, C] (par F i f) - MvPowerSeries.subst ![B, B] (par F i f) =
      PowerSeries.subst (MvPowerSeries.subst ![MvPowerSeries.subst ![x0, x1] F, x2] F) f -
        PowerSeries.subst (MvPowerSeries.subst ![x0, x1] F) f -
        PowerSeries.subst (MvPowerSeries.subst ![x0, x2] F) f -
        PowerSeries.subst (MvPowerSeries.subst ![x1, x2] F) f +
        PowerSeries.subst x0 f + PowerSeries.subst x1 f + PowerSeries.subst x2 f := by
  have c01 := constantCoeff_subst_two_variables F h.1 x0 x1 h0 h1
  have c02 := constantCoeff_subst_two_variables F h.1 x0 x2 h0 h2
  have c12 := constantCoeff_subst_two_variables F h.1 x1 x2 h1 h2
  have c012 := constantCoeff_subst_two_variables F h.1 _ x2 c01 h2
  have l01 := cube_log_add h x0 x1 h0 h1
  have l02 := cube_log_add h x0 x2 h0 h2
  have l12 := cube_log_add h x1 x2 h1 h2
  have l012 := cube_log_add h _ x2 c01 h2
  have lz : PowerSeries.subst (0 : MvPowerSeries ι K) l = 0 :=
    PowerSeries.subst_zero_of_constantCoeff_zero h.2.2.1
  have fz : PowerSeries.subst (0 : MvPowerSeries ι K) f = 0 :=
    PowerSeries.subst_zero_of_constantCoeff_zero hf0
  have e1 : MvPowerSeries.subst ![A, B] F =
      MvPowerSeries.subst ![MvPowerSeries.subst ![x0, x1] F, x2] F :=
    cube_add_eq h A B _ hA hB c012 (by rw [l012, l01]; linear_combination eA + eB)
  have e2 : MvPowerSeries.subst ![A, PowerSeries.subst B i] F = x0 :=
    cube_sub_eq h hi A B _ hA hB h0 (by linear_combination eA)
  have hc := two_mul_C_inv_two (K := K) (ι := ι)
  have sBC : PowerSeries.subst B l + PowerSeries.subst C l = PowerSeries.subst x1 l := by
    linear_combination (MvPowerSeries.C (2 : K)⁻¹) * eB + (MvPowerSeries.C (2 : K)⁻¹) * eC -
      (PowerSeries.subst B l + PowerSeries.subst C l - PowerSeries.subst x1 l) * hc
  have dBC : PowerSeries.subst B l - PowerSeries.subst C l = PowerSeries.subst x2 l := by
    linear_combination (MvPowerSeries.C (2 : K)⁻¹) * eB - (MvPowerSeries.C (2 : K)⁻¹) * eC -
      (PowerSeries.subst B l - PowerSeries.subst C l - PowerSeries.subst x2 l) * hc
  have e3 : MvPowerSeries.subst ![A, C] F = MvPowerSeries.subst ![x0, x1] F :=
    cube_add_eq h A C _ hA hC c01 (by rw [l01]; linear_combination eA + sBC)
  have e4 : MvPowerSeries.subst ![A, PowerSeries.subst C i] F = MvPowerSeries.subst ![x0, x2] F :=
    cube_sub_eq h hi A C _ hA hC c02 (by rw [l02]; linear_combination eA + dBC)
  have e5 : MvPowerSeries.subst ![B, C] F = x1 := cube_add_eq h B C _ hB hC h1 sBC
  have e6 : MvPowerSeries.subst ![B, PowerSeries.subst C i] F = x2 :=
    cube_sub_eq h hi B C _ hB hC h2 dBC
  have e7 : MvPowerSeries.subst ![B, B] F = MvPowerSeries.subst ![x1, x2] F :=
    cube_add_eq h B B _ hB hB c12 (by rw [l12]; linear_combination eB)
  have e8 : MvPowerSeries.subst ![B, PowerSeries.subst B i] F = 0 :=
    cube_sub_eq h hi B B _ hB hB (by simp) (by rw [lz]; ring)
  rw [cube_par_subst F h.1 i f hi.1 A B hA hB, cube_par_subst F h.1 i f hi.1 A C hA hC,
    cube_par_subst F h.1 i f hi.1 B C hB hC, cube_par_subst F h.1 i f hi.1 B B hB hB,
    e1, e2, e3, e4, e5, e6, e7, e8, fz]
  ring

theorem parallelogram_coboundary_three_vars (F : MvPowerSeries (Fin 2) K) (hF : MvPowerSeries.constantCoeff F = 0)
    (f : PowerSeries K) :
    d1 F (cob F f) =
      PowerSeries.subst (MvPowerSeries.subst ![MvPowerSeries.subst
          ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 1] F,
          MvPowerSeries.X 2] F) f -
        PowerSeries.subst (MvPowerSeries.subst
          ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 1] F) f -
        PowerSeries.subst (MvPowerSeries.subst
          ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 2] F) f -
        PowerSeries.subst (MvPowerSeries.subst
          ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 2] F) f +
        PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K) f +
        PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 3) K) f +
        PowerSeries.subst (MvPowerSeries.X 2 : MvPowerSeries (Fin 3) K) f := by
  unfold d1 in3
  rw [cube_cob_subst F hF f _ _ (constantCoeff_subst_two_variables F hF _ _ (by simp) (by simp)) (by simp),
    cube_cob_subst F hF f _ _ (by simp) (by simp), cube_cob_subst F hF f _ _ (by simp) (by simp)]
  ring

theorem cube_simeq_congr {f g f' g' : MvPowerSeries ι K} (h : f - g = f' - g')
    (hs : Simeq f g) : Simeq f' g' := by
  unfold Simeq at hs ⊢
  rw [← h]
  exact hs

theorem integral_mvPowerSeries_X (x : ι) : Integral (MvPowerSeries.X x : MvPowerSeries ι K) := by
  classical
  intro n
  rw [MvPowerSeries.coeff_X]
  split_ifs <;> simp

theorem constantCoeff_eq_zero_of_parallelogram {F : MvPowerSeries (Fin 2) K} {l i f : PowerSeries K} (h : LawLog F l)
    (hi : IsInv l i) (hq : Simeq (par F i f) 0) : PowerSeries.constantCoeff f = 0 := by
  have h0 : MvPowerSeries.constantCoeff (0 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have e := Formalism.G.LogP.constantCoeff_subst_of_zero (par F i f)
    (b := ![(0 : MvPowerSeries (Fin 2) K), 0]) (fun j => by fin_cases j <;> simp)
  have hq0 : MvPowerSeries.constantCoeff (par F i f) = 0 := by simpa using hq.1
  have lz : PowerSeries.subst (0 : MvPowerSeries (Fin 2) K) l = 0 :=
    PowerSeries.subst_zero_of_constantCoeff_zero h.2.2.1
  rw [hq0, cube_par_subst F h.1 i f hi.1 0 0 h0 h0,
    cube_add_eq h 0 0 0 h0 h0 h0 (by rw [lz]; ring),
    cube_sub_eq h hi 0 0 0 h0 h0 h0 (by rw [lz]; ring),
    PowerSeries.subst_zero_eq_C_constantCoeff] at e
  have e' : PowerSeries.constantCoeff f + PowerSeries.constantCoeff f -
      2 * PowerSeries.constantCoeff f - 2 * PowerSeries.constantCoeff f = 0 := by
    have c2 : MvPowerSeries.constantCoeff (2 : MvPowerSeries (Fin 2) K) = 2 :=
      map_ofNat MvPowerSeries.constantCoeff 2
    simpa [c2] using e
  have e2 : (2 : K) * PowerSeries.constantCoeff f = 0 := by linear_combination -e'
  exact (mul_eq_zero.1 e2).resolve_left two_ne_zero

end Norm

section Ultra

variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] {ι : Type}

theorem integral_subst_two_variables {F : MvPowerSeries (Fin 2) K} (hF : Integral F) (U V : MvPowerSeries ι K)
    (hU : MvPowerSeries.constantCoeff U = 0) (hV : MvPowerSeries.constantCoeff V = 0)
    (iU : Integral U) (iV : Integral V) : Integral (MvPowerSeries.subst ![U, V] F) :=
  Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.integral_subst' (fun j => by fin_cases j <;> simpa)
    (fun j => by fin_cases j <;> simpa) hF

theorem integral_subst_one_variable {g : PowerSeries K} (hg : Integral (ι := Unit) g) (U : MvPowerSeries ι K)
    (hU : MvPowerSeries.constantCoeff U = 0) (iU : Integral U) :
    Integral (PowerSeries.subst U g) :=
  Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.integral_subst' (φ := fun _ : Unit => U) (fun _ => hU) (fun _ => iU) hg

theorem cube_simeq_subst2 {q : MvPowerSeries (Fin 2) K} (hq : Simeq q 0) (U V : MvPowerSeries ι K)
    (hU : MvPowerSeries.constantCoeff U = 0) (hV : MvPowerSeries.constantCoeff V = 0)
    (iU : Integral U) (iV : Integral V) : Simeq (MvPowerSeries.subst ![U, V] q) 0 := by
  have e := (equivalence_rules K (Fin 2)).2.2.2.2 ι q 0 ![U, V] (fun j => by fin_cases j <;> simpa)
    (fun j => by fin_cases j <;> simpa) hq
  rwa [subst_zero' (hs2 hU hV)] at e

theorem cube_simeq_subst1 {f g : PowerSeries K} (hq : Simeq (ι := Unit) f g)
    (U : MvPowerSeries ι K) (hU : MvPowerSeries.constantCoeff U = 0) (iU : Integral U) :
    Simeq (PowerSeries.subst U f) (PowerSeries.subst U g) :=
  (equivalence_rules K Unit).2.2.2.2 ι f g (fun _ => U) (fun _ => hU) (fun _ => iU) hq

end Ultra

theorem Cube_of (hH : HalfExists) (hI : SimeqInt) : Cube := by
  intro K _ _ _ F l i f h hi h2 hq
  obtain ⟨hf, hh⟩ := hH K F l h h2
  have hf0 := constantCoeff_eq_zero_of_parallelogram h hi hq
  have c0 : MvPowerSeries.constantCoeff (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K) = 0 := by simp
  have c1 : MvPowerSeries.constantCoeff (MvPowerSeries.X 1 : MvPowerSeries (Fin 3) K) = 0 := by simp
  have c2 : MvPowerSeries.constantCoeff (MvPowerSeries.X 2 : MvPowerSeries (Fin 3) K) = 0 := by simp
  have i0 := integral_mvPowerSeries_X (K := K) (0 : Fin 3)
  have i1 := integral_mvPowerSeries_X (K := K) (1 : Fin 3)
  have i2 := integral_mvPowerSeries_X (K := K) (2 : Fin 3)

  obtain ⟨S, hS⟩ : ∃ S, S = MvPowerSeries.subst
    ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 2] F := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D, D = MvPowerSeries.subst ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 3) K),
    PowerSeries.subst (MvPowerSeries.X 2 : MvPowerSeries (Fin 3) K) i] F := ⟨_, rfl⟩
  have cN := constantCoeff_subst_one_variable i hi.1 _ c2
  have iN := integral_subst_one_variable hi.2.1 _ c2 i2
  have cS : MvPowerSeries.constantCoeff S = 0 := hS ▸ constantCoeff_subst_two_variables F h.1 _ _ c1 c2
  have cD : MvPowerSeries.constantCoeff D = 0 := hD ▸ constantCoeff_subst_two_variables F h.1 _ _ c1 cN
  have iS : Integral S := hS ▸ integral_subst_two_variables h.2.1 _ _ c1 c2 i1 i2
  have iD : Integral D := hD ▸ integral_subst_two_variables h.2.1 _ _ c1 cN i1 iN
  have lS : PowerSeries.subst S l = PowerSeries.subst (MvPowerSeries.X 1) l +
      PowerSeries.subst (MvPowerSeries.X 2) l := hS ▸ cube_log_add h _ _ c1 c2
  have lD : PowerSeries.subst D l = PowerSeries.subst (MvPowerSeries.X 1) l -
      PowerSeries.subst (MvPowerSeries.X 2) l := by
    rw [hD, cube_log_add h _ _ c1 cN, cube_log_inv hi _ c2]; ring
  have cB := constantCoeff_subst_one_variable hf hh.1 S cS
  have cC := constantCoeff_subst_one_variable hf hh.1 D cD
  have iB := integral_subst_one_variable hh.2.1 S cS iS
  have iC := integral_subst_one_variable hh.2.1 D cD iD
  have cA := constantCoeff_subst_two_variables F h.1 _ _ c0 cB
  have iA := integral_subst_two_variables h.2.1 _ _ c0 cB i0 iB
  have key := cube_identity h hi f hf0 (MvPowerSeries.X 0) (MvPowerSeries.X 1) (MvPowerSeries.X 2)
    _ _ _ c0 c1 c2 cA cB cC (cube_log_add h _ _ c0 cB)
    ((cube_log_half hh S cS).trans lS) ((cube_log_half hh D cD).trans lD)
  rw [parallelogram_coboundary_three_vars F h.1 f, ← key]
  have qAB := cube_simeq_subst2 hq _ _ cA cB iA iB
  have qAC := cube_simeq_subst2 hq _ _ cA cC iA iC
  have qBC := cube_simeq_subst2 hq _ _ cB cC iB iC
  have qBB := cube_simeq_subst2 hq _ _ cB cB iB iB
  have s1 := (hI K (Fin 3) _ _ _ _ qAB qAC).1
  have s2 := (equivalence_rules K (Fin 3)).2.2.2.1 _ _ _ _ s1 qBC
  have s3 := (hI K (Fin 3) _ _ _ _ s2 qBB).1
  exact cube_simeq_congr (by ring) s3

theorem diagonal_two_variable_identity : DiagTwo := by
  intro K _ _ _ F l i f h hi hq
  have hf0 := constantCoeff_eq_zero_of_parallelogram h hi hq
  have cX : MvPowerSeries.constantCoeff (PowerSeries.X : PowerSeries K) = 0 :=
    PowerSeries.constantCoeff_X
  have iX : Integral (ι := Unit) (PowerSeries.X : PowerSeries K) := integral_mvPowerSeries_X ()
  have fX : PowerSeries.subst (PowerSeries.X : PowerSeries K) f = f := by
    rw [← PowerSeries.map_algebraMap_eq_subst_X]; simp
  have lz : PowerSeries.subst (0 : PowerSeries K) l = 0 :=
    PowerSeries.subst_zero_of_constantCoeff_zero h.2.2.1
  have fz : PowerSeries.subst (0 : PowerSeries K) f = 0 :=
    PowerSeries.subst_zero_of_constantCoeff_zero hf0
  have q := cube_simeq_subst2 hq _ _ cX cX iX iX
  rw [cube_par_subst F h.1 i f hi.1 _ _ cX cX,
    cube_sub_eq h hi _ _ 0 cX cX (by simp) (by rw [lz]; ring), fz, fX] at q
  refine ⟨cube_simeq_congr (by ring) q, ?_⟩
  rw [cube_cob_subst F h.1 f _ _ cX cX, fX]
  exact cube_simeq_congr (by ring) q

theorem DiagTwo_of (_hI : SimeqInt) : DiagTwo := diagonal_two_variable_identity

theorem CobEven_of (hI : SimeqInt) : CobEven := by
  intro K _ _ _ F l i f h hi hq
  have c0 : MvPowerSeries.constantCoeff (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have c1 : MvPowerSeries.constantCoeff (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have i0 := integral_mvPowerSeries_X (K := K) (0 : Fin 2)
  have i1 := integral_mvPowerSeries_X (K := K) (1 : Fin 2)
  have hs : PowerSeries.HasSubst i := PowerSeries.HasSubst.of_constantCoeff_zero' hi.1
  have comp : ∀ U : MvPowerSeries (Fin 2) K, MvPowerSeries.constantCoeff U = 0 →
      PowerSeries.subst U (PowerSeries.subst i f) = PowerSeries.subst (PowerSeries.subst U i) f :=
    fun U hU => PowerSeries.subst_comp_subst_apply hs (PowerSeries.HasSubst.of_constantCoeff_zero hU) f
  have n0 := constantCoeff_subst_one_variable i hi.1 _ c0
  have n1 := constantCoeff_subst_one_variable i hi.1 _ c1
  have lF : PowerSeries.subst F l = PowerSeries.subst (MvPowerSeries.X 0) l +
      PowerSeries.subst (MvPowerSeries.X 1) l := by
    have e := h.2.2.2.2
    unfold cob at1 at e
    linear_combination e
  have eF : MvPowerSeries.subst ![PowerSeries.subst (MvPowerSeries.X 0) i,
      PowerSeries.subst (MvPowerSeries.X 1) i] F = PowerSeries.subst F i :=
    cube_add_eq h _ _ _ n0 n1 (constantCoeff_subst_one_variable i hi.1 F h.1)
      (by rw [cube_log_inv hi _ c0, cube_log_inv hi _ c1, cube_log_inv hi F h.1, lF]; ring)
  have qF := cube_simeq_subst1 hq F h.1 h.2.1
  have q0 := cube_simeq_subst1 hq _ c0 i0
  have q1 := cube_simeq_subst1 hq _ c1 i1
  rw [comp F h.1] at qF
  rw [comp _ c0] at q0
  rw [comp _ c1] at q1
  have s1 := (hI K (Fin 2) _ _ _ _ qF q0).1
  have s2 := (hI K (Fin 2) _ _ _ _ s1 q1).1
  unfold at1
  rw [cube_cob_subst F h.1 f _ _ n0 n1, eF]
  exact s2

end Formalism.L2.Th1.B
