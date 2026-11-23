import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.FinalB
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.StatementC

noncomputable section

namespace Formalism.L2.Th1.B.Mul

open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob d1 in3 swap2 DivAB equivalence_rules)
open Formalism.G.LogP (hs2 hs3 subst2_subst psubst_subst subst_zero')

section Grp

variable {A : Type} [AddCommGroup A]

theorem add_rule (g : ℤ → A) (h : ∀ n m, g (n + m) = g n + g m) (n : ℤ) : g n = n • g 1 := by
  have e := map_zsmul (AddMonoidHom.mk' g h) n 1
  simpa using e

theorem quad_rule (g : ℤ → A) (h0 : g 0 = 0)
    (h : ∀ n m, g (n + m) + g (n - m) = g n + g n + g m + g m) (n : ℤ) :
    g n = (n ^ 2) • g 1 := by
  have ev : ∀ m, g (-m) = g m := by
    intro m
    have e := h 0 m
    rw [zero_add, zero_sub, h0] at e
    have e' : g (-m) = 0 + 0 + g m + g m - g m := eq_sub_of_add_eq' e
    rw [e']
    abel
  have nat : ∀ k : ℕ, g k = ((k : ℤ) ^ 2) • g 1 ∧ g ((k : ℤ) + 1) = (((k : ℤ) + 1) ^ 2) • g 1 := by
    intro k
    induction k with
    | zero => simp [h0]
    | succ k ih =>
      refine ⟨by push_cast; exact ih.2, ?_⟩
      have e := h ((k : ℤ) + 1) 1
      rw [add_sub_cancel_right, ih.1, ih.2] at e
      have e' := eq_sub_of_add_eq e
      push_cast
      rw [e']
      module
  obtain ⟨k, rfl | rfl⟩ := n.eq_nat_or_neg
  · exact (nat k).1
  · rw [ev, (nat k).1, neg_sq]

end Grp

section Quot

variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] {ι : Type}

def lam (K ι : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] :
    AddSubgroup (MvPowerSeries ι K) where
  carrier := {h | Simeq h 0}
  zero_mem' := (equivalence_rules K ι).1 0
  add_mem' := fun {a b} ha hb => by
    have e := (equivalence_rules K ι).2.2.2.1 a 0 b 0 ha hb
    rwa [add_zero] at e
  neg_mem' := fun {a} ha => by
    have e := (simeqInt K ι a 0 a 0 ha ha).2.1
    rwa [neg_zero] at e

def cl (f : MvPowerSeries ι K) : MvPowerSeries ι K ⧸ lam K ι := QuotientAddGroup.mk' (lam K ι) f

theorem simeq_iff_cl (f g : MvPowerSeries ι K) : Simeq f g ↔ cl f = cl g := by
  unfold cl
  rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_iff_sub_mem]
  exact ⟨cube_simeq_congr (by ring), cube_simeq_congr (by ring)⟩

theorem cl_add (f g : MvPowerSeries ι K) : cl (f + g) = cl f + cl g := map_add _ f g

theorem cl_sub (f g : MvPowerSeries ι K) : cl (f - g) = cl f - cl g := map_sub _ f g

theorem cl_zero : cl (0 : MvPowerSeries ι K) = 0 := map_zero _

theorem cl_int (n : ℤ) (f : MvPowerSeries ι K) : cl ((n : MvPowerSeries ι K) * f) = n • cl f := by
  rw [← zsmul_eq_mul]
  exact map_zsmul _ n f

end Quot

section Law

variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K]

def IsMul (l : PowerSeries K) (n : ℤ) (N : PowerSeries K) : Prop :=
  PowerSeries.constantCoeff N = 0 ∧ Integral (ι := Unit) N ∧
    PowerSeries.subst N l = PowerSeries.C (n : K) * l

theorem subst_X_self (f : PowerSeries K) : PowerSeries.subst (PowerSeries.X : PowerSeries K) f = f :=
  PowerSeries.X_subst f

theorem isMul_zero {l : PowerSeries K} (hl : PowerSeries.constantCoeff l = 0) : IsMul l 0 0 := by
  refine ⟨map_zero _, law_integral_zero, ?_⟩
  rw [law_subst_zero l hl]
  simp

theorem isMul_one (l : PowerSeries K) : IsMul l 1 PowerSeries.X := by
  refine ⟨PowerSeries.constantCoeff_X, law_integral_X (), ?_⟩
  rw [subst_X_self]
  simp

theorem isMul_neg_one {l i : PowerSeries K} (hi : IsInv l i) : IsMul l (-1) i := by
  refine ⟨hi.1, hi.2.1, ?_⟩
  rw [hi.2.2]
  simp

theorem isMul_add {F : MvPowerSeries (Fin 2) K} {l : PowerSeries K} (h : LawLog F l) {n m : ℤ}
    {N M : PowerSeries K} (hN : IsMul l n N) (hM : IsMul l m M) :
    IsMul l (n + m) (MvPowerSeries.subst ![N, M] F) := by
  refine ⟨constantCoeff_subst_two_variables F h.1 N M hN.1 hM.1, integral_subst_two_variables h.2.1 N M hN.1 hM.1 hN.2.1 hM.2.1, ?_⟩
  rw [cube_log_add h N M hN.1 hM.1, hN.2.2, hM.2.2]
  push_cast
  rw [map_add]
  ring

theorem isMul_exists {F : MvPowerSeries (Fin 2) K} {l : PowerSeries K} (h : LawLog F l) (n : ℤ) :
    ∃ N, IsMul l n N := by
  obtain ⟨i, hi⟩ := invExists K F l h
  induction n using Int.induction_on with
  | zero => exact ⟨0, isMul_zero h.2.2.1⟩
  | succ k ih =>
    obtain ⟨N, hN⟩ := ih
    exact ⟨_, isMul_add h hN (isMul_one l)⟩
  | pred k ih =>
    obtain ⟨N, hN⟩ := ih
    exact ⟨_, isMul_add h hN (isMul_neg_one hi)⟩

def mulN {F : MvPowerSeries (Fin 2) K} {l : PowerSeries K} (h : LawLog F l) (n : ℤ) :
    PowerSeries K := (isMul_exists h n).choose

theorem mulN_spec {F : MvPowerSeries (Fin 2) K} {l : PowerSeries K} (h : LawLog F l) (n : ℤ) :
    IsMul l n (mulN h n) := (isMul_exists h n).choose_spec

theorem mulN_eq {F : MvPowerSeries (Fin 2) K} {l : PowerSeries K} (h : LawLog F l) (n : ℤ)
    (N : PowerSeries K) (hN0 : PowerSeries.constantCoeff N = 0)
    (hN : PowerSeries.subst N l = PowerSeries.C (n : K) * l) : N = mulN h n :=
  log_inj l h.2.2.1 h.2.2.2.1 N (mulN h n) hN0 (mulN_spec h n).1
    (hN.trans (mulN_spec h n).2.2.symm)

theorem mulN_zero {F : MvPowerSeries (Fin 2) K} {l : PowerSeries K} (h : LawLog F l) :
    mulN h 0 = 0 :=
  (mulN_eq h 0 0 (isMul_zero h.2.2.1).1 (isMul_zero h.2.2.1).2.2).symm

theorem mulN_one {F : MvPowerSeries (Fin 2) K} {l : PowerSeries K} (h : LawLog F l) :
    mulN h 1 = PowerSeries.X :=
  (mulN_eq h 1 _ (isMul_one l).1 (isMul_one l).2.2).symm

theorem mulN_add {F : MvPowerSeries (Fin 2) K} {l : PowerSeries K} (h : LawLog F l) (n m : ℤ) :
    MvPowerSeries.subst ![mulN h n, mulN h m] F = mulN h (n + m) :=
  have e := isMul_add h (mulN_spec h n) (mulN_spec h m)
  mulN_eq h (n + m) _ e.1 e.2.2

theorem mulN_sub {F : MvPowerSeries (Fin 2) K} {l i : PowerSeries K} (h : LawLog F l)
    (hi : IsInv l i) (n m : ℤ) :
    MvPowerSeries.subst ![mulN h n, PowerSeries.subst (mulN h m) i] F = mulN h (n - m) := by
  refine cube_sub_eq h hi _ _ _ (mulN_spec h n).1 (mulN_spec h m).1 (mulN_spec h (n - m)).1 ?_
  rw [(mulN_spec h n).2.2, (mulN_spec h m).2.2, (mulN_spec h (n - m)).2.2]
  push_cast
  rw [map_sub]
  ring

end Law

theorem formal_multiplication_exists : MulExists := by
  intro K _ _ _ F l h n
  exact isMul_exists h n

theorem multiplication_square_holds : MulSq := by
  intro K _ _ _ F l i f h hi hq n N hN0 hN
  have hf0 := constantCoeff_eq_zero_of_parallelogram h hi hq
  rw [mulN_eq h n N hN0 hN, simeq_iff_cl, cl_int]
  have key := quad_rule (fun k : ℤ => cl (PowerSeries.subst (mulN h k) f : PowerSeries K))
    (by
      show cl (PowerSeries.subst (mulN h 0) f : PowerSeries K) = 0
      rw [mulN_zero, law_subst_zero f hf0, cl_zero])
    (by
      intro a b
      have q := cube_simeq_subst2 hq _ _ (mulN_spec h a).1 (mulN_spec h b).1 (mulN_spec h a).2.1
        (mulN_spec h b).2.1
      rw [cube_par_subst F h.1 i f hi.1 _ _ (mulN_spec h a).1 (mulN_spec h b).1, mulN_add,
        mulN_sub h hi, simeq_iff_cl, cl_zero, two_mul, two_mul, cl_sub, cl_sub, cl_add, cl_add,
        cl_add] at q
      show cl (PowerSeries.subst (mulN h (a + b)) f : PowerSeries K) +
        cl (PowerSeries.subst (mulN h (a - b)) f : PowerSeries K) = _
      rw [sub_sub, sub_eq_zero] at q
      rw [q]
      abel) n
  have key' : cl (PowerSeries.subst (mulN h n) f : PowerSeries K) =
      (n ^ 2) • cl (PowerSeries.subst (mulN h 1) f : PowerSeries K) := key
  rw [key', mulN_one, subst_X_self]

theorem multiplication_additive_holds : AddMul := by
  intro K _ _ _ F l f h hq n N hN0 hN
  rw [mulN_eq h n N hN0 hN, simeq_iff_cl, cl_int]
  have key := add_rule (fun k : ℤ => cl (PowerSeries.subst (mulN h k) f : PowerSeries K))
    (by
      intro a b
      have q := cube_simeq_subst2 hq _ _ (mulN_spec h a).1 (mulN_spec h b).1 (mulN_spec h a).2.1
        (mulN_spec h b).2.1
      rw [cube_cob_subst F h.1 f _ _ (mulN_spec h a).1 (mulN_spec h b).1, mulN_add,
        simeq_iff_cl, cl_zero, cl_sub, cl_sub, sub_sub, sub_eq_zero] at q
      exact q) n
  have key' : cl (PowerSeries.subst (mulN h n) f : PowerSeries K) =
      n • cl (PowerSeries.subst (mulN h 1) f : PowerSeries K) := key
  rw [key', mulN_one, subst_X_self]

section Two

variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] {ι : Type}

theorem subst_first_coboundary (F be : MvPowerSeries (Fin 2) K) (hF : MvPowerSeries.constantCoeff F = 0)
    (U V W : MvPowerSeries ι K) (hU : MvPowerSeries.constantCoeff U = 0)
    (hV : MvPowerSeries.constantCoeff V = 0) (hW : MvPowerSeries.constantCoeff W = 0) :
    MvPowerSeries.subst ![U, V, W] (d1 F be) =
      MvPowerSeries.subst ![MvPowerSeries.subst ![U, V] F, W] be -
        MvPowerSeries.subst ![U, W] be - MvPowerSeries.subst ![V, W] be := by
  have hb := hs3 hU hV hW
  have c3 : MvPowerSeries.constantCoeff (in3 F) = 0 := constantCoeff_subst_two_variables F hF _ _ (by simp) (by simp)
  unfold d1
  rw [← MvPowerSeries.coe_substAlgHom hb, map_sub, map_sub, MvPowerSeries.coe_substAlgHom hb,
    subst2_subst be c3 (by simp) hb, subst2_subst be (by simp) (by simp) hb,
    subst2_subst be (by simp) (by simp) hb]
  unfold in3
  rw [subst2_subst F (by simp) (by simp) hb, MvPowerSeries.subst_X hb, MvPowerSeries.subst_X hb,
    MvPowerSeries.subst_X hb]
  rfl

theorem simeq_subst3 {q : MvPowerSeries (Fin 3) K} (hq : Simeq q 0) (U V W : MvPowerSeries ι K)
    (hU : MvPowerSeries.constantCoeff U = 0) (hV : MvPowerSeries.constantCoeff V = 0)
    (hW : MvPowerSeries.constantCoeff W = 0) (iU : Integral U) (iV : Integral V)
    (iW : Integral W) : Simeq (MvPowerSeries.subst ![U, V, W] q) 0 := by
  have e := (equivalence_rules K (Fin 3)).2.2.2.2 ι q 0 ![U, V, W]
    (fun j => by fin_cases j <;> simpa) (fun j => by fin_cases j <;> simpa) hq
  rwa [subst_zero' (hs3 hU hV hW)] at e

theorem formal_multiplication_add {F : MvPowerSeries (Fin 2) K} {l : PowerSeries K} (h : LawLog F l) (n m : ℤ)
    (x : ι) :
    MvPowerSeries.subst ![at1 x (mulN h n), at1 x (mulN h m)] F = at1 x (mulN h (n + m)) := by
  rw [← mulN_add h n m]
  exact (subst2_subst F (mulN_spec h n).1 (mulN_spec h m).1
    (PowerSeries.HasSubst.X x).const).symm

end Two

theorem multiplication_biadditive_holds : BiaddMul := by
  intro K _ _ _ F be l h hq n N hN0 hN
  rw [mulN_eq h n N hN0 hN, simeq_iff_cl, cl_int]
  have c1 : MvPowerSeries.constantCoeff (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have key := add_rule (fun k : ℤ => cl (MvPowerSeries.subst
      ![at1 0 (mulN h k), (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K)] be))
    (by
      intro a b
      have ca := constantCoeff_series_at_variable (0 : Fin 2) _ (mulN_spec h a).1
      have cb := constantCoeff_series_at_variable (0 : Fin 2) _ (mulN_spec h b).1
      have q := simeq_subst3 hq _ _ _ ca cb c1 (integral_series_at_variable 0 _ (mulN_spec h a).2.1)
        (integral_series_at_variable 0 _ (mulN_spec h b).2.1) (law_integral_X 1)
      rw [subst_first_coboundary F be h.1 _ _ _ ca cb c1, formal_multiplication_add,
        simeq_iff_cl, cl_zero, cl_sub, cl_sub, sub_sub, sub_eq_zero] at q
      exact q) n
  have key' : cl (MvPowerSeries.subst
      ![at1 0 (mulN h n), (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K)] be) =
      n • cl (MvPowerSeries.subst
      ![at1 0 (mulN h 1), (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K)] be) := key
  have e1 : at1 (0 : Fin 2) (PowerSeries.X : PowerSeries K) = MvPowerSeries.X 0 :=
    PowerSeries.subst_X (PowerSeries.HasSubst.X 0)
  rw [key', mulN_one, e1, Formalism.G.LogP.subst_XX]

end Formalism.L2.Th1.B.Mul
