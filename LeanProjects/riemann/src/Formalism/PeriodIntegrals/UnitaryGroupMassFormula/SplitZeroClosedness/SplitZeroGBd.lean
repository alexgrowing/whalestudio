import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SplitZeroClosedness.ZcFacts

noncomputable section

open Classical

namespace PI.SZGW

open PI.BeDiagZp PI.BeDiagZp.Asm PI.BeDiagZp.ContPf

theorem Scale {p : ℕ} [Fact p.Prime] (hZS : ZpSimeq)
    (zMul : ∀ a b : ℤ_[p], zc (a * b) = zc a * zc b) (zOne : zc (1 : ℤ_[p]) = 1)
    {τ : Type} (F : MvPowerSeries τ ℂ_[p]) (u : ℤ_[p]) (hu : IsUnit u)
    (H : Simeq (MvPowerSeries.C (zc u) * F) 0) : Simeq F 0 := by
  have hN : ∀ n : ℕ, Simeq ((fun c : ℂ_[p] => MvPowerSeries.C c * (MvPowerSeries.C (zc u) * F)) (n : ℂ_[p])) 0 := by
    intro n
    induction n with
    | zero => simp only [Nat.cast_zero, map_zero, zero_mul]; exact simeq_refl 0
    | succ n ih =>
      have H2 := simeq_add ih H
      refine simeq_congr ?_ H2
      simp only [Nat.cast_succ, map_add, map_one, add_mul, one_mul, add_zero, sub_zero]
  have hGs : CC fun c : ℂ_[p] => MvPowerSeries.C c * (MvPowerSeries.C (zc u) * F) := cc_mul cc_C (cc_const _)
  obtain ⟨w, hw⟩ := hu.exists_left_inv
  have H3 := hZS p τ _ hGs hN w
  have e : zc w * zc u = 1 := by rw [← zMul, hw, zOne]
  refine simeq_congr ?_ H3
  show MvPowerSeries.C (zc w) * (MvPowerSeries.C (zc u) * F) - 0 = F - 0
  rw [← mul_assoc, ← map_mul, e, map_one, one_mul]

section Steps

variable {p : ℕ} [Fact p.Prime] {l ex ph : PowerSeries ℂ_[p]}
  (hex : PowerSeries.constantCoeff ex = 0) (hlex : PowerSeries.subst ex l = PowerSeries.X)

include hex hlex

theorem hl0 : PowerSeries.constantCoeff l = 0 := (IdentW.ident_holds p l ex hex hlex).1

theorem cA {σ : Type} (a b : MvPowerSeries σ ℂ_[p]) (ha : MvPowerSeries.constantCoeff a = 0)
    (hb : MvPowerSeries.constantCoeff b = 0) : MvPowerSeries.constantCoeff (add l ex a b) = 0 :=
  ((IdentW.ident_holds p l ex hex hlex).2 _ a b ha hb).1

theorem cM {σ : Type} (c : ℂ_[p]) (a : MvPowerSeries σ ℂ_[p]) (ha : MvPowerSeries.constantCoeff a = 0) :
    MvPowerSeries.constantCoeff (mulBy l ex c a) = 0 :=
  ((IdentW.ident_holds p l ex hex hlex).2 _ a a ha ha).2.1 c

theorem comm {σ : Type} (a b : MvPowerSeries σ ℂ_[p]) (ha : MvPowerSeries.constantCoeff a = 0)
    (hb : MvPowerSeries.constantCoeff b = 0) : add l ex a b = add l ex b a :=
  ((IdentW.ident_holds p l ex hex hlex).2 _ a b ha hb).2.2.1

theorem addM {σ : Type} (a : MvPowerSeries σ ℂ_[p]) (ha : MvPowerSeries.constantCoeff a = 0) (c d : ℂ_[p]) :
    add l ex (mulBy l ex c a) (mulBy l ex d a) = mulBy l ex (c + d) a :=
  ((IdentW.ident_holds p l ex hex hlex).2 _ a a ha ha).2.2.2.2.1 c d

theorem addS {σ : Type} (a : MvPowerSeries σ ℂ_[p]) (ha : MvPowerSeries.constantCoeff a = 0) (c : ℂ_[p]) :
    add l ex (mulBy l ex c a) a = mulBy l ex (c + 1) a :=
  ((IdentW.ident_holds p l ex hex hlex).2 _ a a ha ha).2.2.2.2.2.1 c

theorem mul1 {σ : Type} (a : MvPowerSeries σ ℂ_[p]) (ha : MvPowerSeries.constantCoeff a = 0) :
    mulBy l ex 1 a = a :=
  ((IdentW.ident_holds p l ex hex hlex).2 _ a a ha ha).2.2.2.2.2.2.1

theorem mul0 {σ : Type} (a : MvPowerSeries σ ℂ_[p]) (ha : MvPowerSeries.constantCoeff a = 0) :
    mulBy l ex 0 a = 0 :=
  ((IdentW.ident_holds p l ex hex hlex).2 _ a a ha ha).2.2.2.2.2.2.2

theorem bsym {σ : Type} (a b : MvPowerSeries σ ℂ_[p]) (ha : MvPowerSeries.constantCoeff a = 0)
    (hb : MvPowerSeries.constantCoeff b = 0) : be l ex ph a b = be l ex ph b a := by
  simp only [be]
  rw [comm hex hlex a b ha hb]
  abel

theorem addZ {σ : Type} (a : MvPowerSeries σ ℂ_[p]) (ha : MvPowerSeries.constantCoeff a = 0) :
    add l ex a 0 = a := by
  have e := addM hex hlex a ha 1 0
  rw [mul1 hex hlex a ha, mul0 hex hlex a ha, add_zero, mul1 hex hlex a ha] at e
  exact e

theorem K2 (hbi : Simeq (be l ex ph (add l ex (Xv 0) (Xv 1)) (Xv 2) : MvPowerSeries (Fin 3) ℂ_[p])
      (be l ex ph (Xv 0) (Xv 2) + be l ex ph (Xv 1) (Xv 2)))
    {τ : Type} (a b c : MvPowerSeries τ ℂ_[p]) (ha : MvPowerSeries.constantCoeff a = 0)
    (hb : MvPowerSeries.constantCoeff b = 0) (hc : MvPowerSeries.constantCoeff c = 0)
    (ia : IntegralMv a) (ib : IntegralMv b) (ic : IntegralMv c) :
    Simeq (be l ex ph (add l ex a b) c) (be l ex ph a c + be l ex ph b c) := by
  have hs : ∀ i, MvPowerSeries.constantCoeff (![a, b, c] i) = 0 := by
    intro i; fin_cases i <;> simpa
  have is : ∀ i, IntegralMv (![a, b, c] i) := by
    intro i; fin_cases i <;> simpa
  have H := power_series_diagonal_linear p (Fin 3) τ _ _ ![a, b, c] hs is hbi
  obtain ⟨hsX, -, hsA, hr⟩ := OpsW.substOps_holds p l ex ph hex (hl0 hex hlex) (Fin 3) τ ![a, b, c] hs
  have e1 := (hr _ _ (cA hex hlex _ _ (ccX (0 : Fin 3)) (ccX (1 : Fin 3))) (ccX (2 : Fin 3))).2.2.2.2
  have e2 := (hr _ _ (ccX (0 : Fin 3)) (ccX (1 : Fin 3))).2.1
  have e3 := (hr _ _ (ccX (0 : Fin 3)) (ccX (2 : Fin 3))).2.2.2.2
  have e4 := (hr _ _ (ccX (1 : Fin 3)) (ccX (2 : Fin 3))).2.2.2.2
  simp only [hsA, e1, e2, e3, e4, hsX] at H
  simpa using H

theorem Nint (hgrp : IntegralMv (add l ex (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]))
    {τ : Type} (a : MvPowerSeries τ ℂ_[p]) (ha : MvPowerSeries.constantCoeff a = 0) (ia : IntegralMv a)
    (n : ℕ) : IntegralMv (mulBy l ex (n : ℂ_[p]) a) := by
  induction n with
  | zero => rw [Nat.cast_zero, mul0 hex hlex a ha]; exact int0
  | succ n ih =>
    rw [Nat.cast_succ, ← addS hex hlex a ha]
    have hs : ∀ i, MvPowerSeries.constantCoeff (![mulBy l ex (n : ℂ_[p]) a, a] i) = 0 := by
      intro i; fin_cases i
      · simpa using cM hex hlex (n : ℂ_[p]) a ha
      · simpa using ha
    have is : ∀ i, IntegralMv (![mulBy l ex (n : ℂ_[p]) a, a] i) := by
      intro i; fin_cases i
      · simpa using ih
      · simpa using ia
    have H := intSubst_holds p (Fin 2) τ _ _ hs is hgrp
    obtain ⟨hsX, -, -, hr⟩ := OpsW.substOps_holds p l ex 0 hex (hl0 hex hlex) (Fin 2) τ _ hs
    rw [(hr _ _ (ccX (0 : Fin 2)) (ccX (1 : Fin 2))).2.1, hsX, hsX] at H
    simpa using H

theorem Lnat (hgrp : IntegralMv (add l ex (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]))
    (hbi : Simeq (be l ex ph (add l ex (Xv 0) (Xv 1)) (Xv 2) : MvPowerSeries (Fin 3) ℂ_[p])
      (be l ex ph (Xv 0) (Xv 2) + be l ex ph (Xv 1) (Xv 2))) (n : ℕ) :
    Simeq (be l ex ph (mulBy l ex (n : ℂ_[p]) (Xv 0)) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p])
      (MvPowerSeries.C (n : ℂ_[p]) * be l ex ph (Xv 0) (Xv 1)) := by
  have c0 : MvPowerSeries.constantCoeff (Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) = 0 := ccX 0
  have c1 : MvPowerSeries.constantCoeff (Xv 1 : MvPowerSeries (Fin 2) ℂ_[p]) = 0 := ccX 1
  induction n with
  | zero =>
    have H := simeq_symm (K2 hex hlex hbi (0 : MvPowerSeries (Fin 2) ℂ_[p]) 0 (Xv 1) (map_zero _) (map_zero _) c1
      int0 int0 (intX 1))
    refine simeq_congr ?_ H
    rw [Nat.cast_zero, mul0 hex hlex _ c0, map_zero, zero_mul, sub_zero,
      addZ hex hlex (0 : MvPowerSeries (Fin 2) ℂ_[p]) (map_zero _)]
    abel
  | succ n ih =>
    have cN := cM hex hlex (n : ℂ_[p]) _ c0
    rw [Nat.cast_succ, ← addS hex hlex _ c0]
    have H := K2 hex hlex hbi _ _ _ cN c0 c1 (Nint hex hlex hgrp _ c0 (intX 0) n) (intX 0) (intX 1)
    refine simeq_trans H ?_
    have H2 := simeq_add ih (simeq_refl (be l ex ph (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]))
    refine simeq_congr ?_ H2
    rw [map_add, map_one, add_mul, one_mul]

theorem Lzp (hZS : ZpSimeq) (hgrp : IntegralMv (add l ex (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]))
    (hbi : Simeq (be l ex ph (add l ex (Xv 0) (Xv 1)) (Xv 2) : MvPowerSeries (Fin 3) ℂ_[p])
      (be l ex ph (Xv 0) (Xv 2) + be l ex ph (Xv 1) (Xv 2))) (c : ℤ_[p]) :
    Simeq (be l ex ph (mulBy l ex (zc c) (Xv 0)) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p])
      (MvPowerSeries.C (zc c) * be l ex ph (Xv 0) (Xv 1)) := by
  have hl := hl0 hex hlex
  have c0 : MvPowerSeries.constantCoeff (Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) = 0 := ccX 0
  have c1 : MvPowerSeries.constantCoeff (Xv 1 : MvPowerSeries (Fin 2) ℂ_[p]) = 0 := ccX 1
  have hlx : MvPowerSeries.constantCoeff (PowerSeries.subst (Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) l) = 0 :=
    constantCoeff_powerSeries_subst_eq_zero_diagonal_padic_substitution _ c0 l hl
  have hly : MvPowerSeries.constantCoeff (PowerSeries.subst (Xv 1 : MvPowerSeries (Fin 2) ℂ_[p]) l) = 0 :=
    constantCoeff_powerSeries_subst_eq_zero_diagonal_padic_substitution _ c1 l hl
  have hM0 : ∀ c : ℂ_[p], MvPowerSeries.constantCoeff (mulBy l ex c (Xv 0 : MvPowerSeries (Fin 2) ℂ_[p])) = 0 :=
    fun c => cM hex hlex c _ c0
  have hM : CC fun c : ℂ_[p] => mulBy l ex c (Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) := by
    apply cc_subst ex (fun c => by simp [hlx]) (cc_mul cc_C (cc_const _))
  have hA0 : ∀ c : ℂ_[p], MvPowerSeries.constantCoeff
      (add l ex (mulBy l ex c (Xv 0)) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) = 0 :=
    fun c => cA hex hlex _ _ (hM0 c) c1
  have hA : CC fun c : ℂ_[p] => (add l ex (mulBy l ex c (Xv 0)) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) := by
    apply cc_subst ex (fun c => by simp [constantCoeff_powerSeries_subst_eq_zero_diagonal_padic_substitution _ (hM0 c) l hl, hly])
    exact cc_add (cc_subst l hM0 hM) (cc_const _)
  have hG : CC fun c : ℂ_[p] => (be l ex ph (mulBy l ex c (Xv 0)) (Xv 1) -
      MvPowerSeries.C c * be l ex ph (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) := by
    refine cc_sub ?_ (cc_mul cc_C (cc_const _))
    unfold be phAt
    exact cc_sub (cc_sub (cc_subst ph hA0 hA) (cc_subst ph hM0 hM)) (cc_const _)
  have H := hZS p (Fin 2) _ hG (fun n => simeq_congr (by rw [sub_zero]) (Lnat hex hlex hgrp hbi n)) c
  exact simeq_congr (by rw [sub_zero]) H

theorem Lzp2 (hZS : ZpSimeq) (hgrp : IntegralMv (add l ex (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]))
    (hbi : Simeq (be l ex ph (add l ex (Xv 0) (Xv 1)) (Xv 2) : MvPowerSeries (Fin 3) ℂ_[p])
      (be l ex ph (Xv 0) (Xv 2) + be l ex ph (Xv 1) (Xv 2))) (c : ℤ_[p]) :
    Simeq (be l ex ph (Xv 0) (mulBy l ex (zc c) (Xv 1)) : MvPowerSeries (Fin 2) ℂ_[p])
      (MvPowerSeries.C (zc c) * be l ex ph (Xv 0) (Xv 1)) := by
  have c0 : MvPowerSeries.constantCoeff (Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) = 0 := ccX 0
  have c1 : MvPowerSeries.constantCoeff (Xv 1 : MvPowerSeries (Fin 2) ℂ_[p]) = 0 := ccX 1
  have hs : ∀ i, MvPowerSeries.constantCoeff
      (![(Xv 1 : MvPowerSeries (Fin 2) ℂ_[p]), Xv 0] i) = 0 := by
    intro i; fin_cases i
    · simpa using c1
    · simpa using c0
  have is : ∀ i, IntegralMv (![(Xv 1 : MvPowerSeries (Fin 2) ℂ_[p]), Xv 0] i) := by
    intro i; fin_cases i
    · simpa using (intX 1 : IntegralMv (Xv 1 : MvPowerSeries (Fin 2) ℂ_[p]))
    · simpa using (intX 0 : IntegralMv (Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]))
  have H := power_series_diagonal_linear p (Fin 2) (Fin 2) _ _ _ hs is (Lzp hex hlex hZS hgrp hbi c)
  obtain ⟨hsX, hsC, -, hr⟩ := OpsW.substOps_holds p l ex ph hex (hl0 hex hlex) (Fin 2) (Fin 2) _ hs
  have e1 := (hr _ _ (cM hex hlex (zc c) _ c0) c1).2.2.2.2
  have e2 := (hr _ _ c0 c0).2.2.1 (zc c)
  have e3 := (hr _ _ c0 c1).2.2.2.2
  rw [hsC, e1, e2, e3] at H
  simp only [hsX, Matrix.cons_val_zero, Matrix.cons_val_one] at H
  rw [bsym hex hlex _ _ (cM hex hlex _ _ c1) c0, bsym hex hlex _ _ c1 c0] at H
  exact H

theorem hB (hZS : ZpSimeq) (hZC : ZcFacts) (hp2 : p ≠ 2)
    (hgrp : IntegralMv (add l ex (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]))
    (hbi : Simeq (be l ex ph (add l ex (Xv 0) (Xv 1)) (Xv 2) : MvPowerSeries (Fin 3) ℂ_[p])
      (be l ex ph (Xv 0) (Xv 2) + be l ex ph (Xv 1) (Xv 2))) (a b : ℤ_[p]) (hu : IsUnit (a - b))
    (hc : Simeq (be l ex ph (mulBy l ex (zc a) (Xv 0)) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p])
      (be l ex ph (Xv 0) (mulBy l ex (zc b) (Xv 1)))) :
    Simeq (be l ex ph (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) 0 := by
  obtain ⟨zMul, zSub, zOne, -, -, -⟩ := hZC p hp2
  have D : Simeq (MvPowerSeries.C (zc (a - b)) * be l ex ph (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) 0 := by
    have H := simeq_trans (simeq_trans (simeq_symm (Lzp hex hlex hZS hgrp hbi a)) hc) (Lzp2 hex hlex hZS hgrp hbi b)
    refine simeq_congr ?_ H
    rw [zSub, map_sub, sub_mul, sub_zero]
  exact Scale hZS zMul zOne _ (a - b) hu D

theorem iNeg (hZI : ZpInt) (hZC : ZcFacts) (hp2 : p ≠ 2)
    (hgrp : IntegralMv (add l ex (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p])) :
    IntegralMv (mulBy l ex (-1) (Xv () : MvPowerSeries Unit ℂ_[p])) := by
  obtain ⟨-, -, -, zNeg, -, -⟩ := hZC p hp2
  have ccU : MvPowerSeries.constantCoeff (Xv () : MvPowerSeries Unit ℂ_[p]) = 0 := ccX ()
  have hlu := constantCoeff_powerSeries_subst_eq_zero_diagonal_padic_substitution _ ccU l (hl0 hex hlex)
  have hMU : CC fun c : ℂ_[p] => mulBy l ex c (Xv () : MvPowerSeries Unit ℂ_[p]) := by
    apply cc_subst ex (fun c => by simp [hlu]) (cc_mul cc_C (cc_const _))
  have H := hZI p Unit _ hMU (fun n => Nint hex hlex hgrp _ ccU (intX ()) n) (-1)
  rw [zNeg] at H
  exact H

theorem hPh (hZS : ZpSimeq) (hZI : ZpInt) (hZC : ZcFacts) (hp2 : p ≠ 2)
    (hgrp : IntegralMv (add l ex (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]))
    (hB : Simeq (be l ex ph (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) 0)
    (hphi : Simeq (phAt ph (mulBy l ex (-1) (Xv ())) : MvPowerSeries Unit ℂ_[p]) (phAt ph (Xv ()))) :
    Simeq (phAt ph (Xv ()) : MvPowerSeries Unit ℂ_[p]) 0 := by
  obtain ⟨zMul, -, zOne, -, zTwo, uTwo⟩ := hZC p hp2
  have c0 : MvPowerSeries.constantCoeff (Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) = 0 := ccX 0
  have c1 : MvPowerSeries.constantCoeff (Xv 1 : MvPowerSeries (Fin 2) ℂ_[p]) = 0 := ccX 1
  have ccU : MvPowerSeries.constantCoeff (Xv () : MvPowerSeries Unit ℂ_[p]) = 0 := ccX ()
  have P1 : Simeq (be l ex ph (Xv ()) (mulBy l ex (-1) (Xv ())) : MvPowerSeries Unit ℂ_[p]) 0 := by
    have hs : ∀ i, MvPowerSeries.constantCoeff
        (![(Xv () : MvPowerSeries Unit ℂ_[p]), mulBy l ex (-1) (Xv ())] i) = 0 := by
      intro i; fin_cases i
      · simpa using ccU
      · simpa using cM hex hlex (-1) _ ccU
    have is : ∀ i, IntegralMv (![(Xv () : MvPowerSeries Unit ℂ_[p]), mulBy l ex (-1) (Xv ())] i) := by
      intro i; fin_cases i
      · simpa using (intX () : IntegralMv (Xv () : MvPowerSeries Unit ℂ_[p]))
      · simpa using iNeg hex hlex hZI hZC hp2 hgrp
    have H := power_series_diagonal_linear p (Fin 2) Unit _ _ _ hs is hB
    obtain ⟨hsX, hsC, -, hr⟩ := OpsW.substOps_holds p l ex ph hex (hl0 hex hlex) (Fin 2) Unit _ hs
    have z : MvPowerSeries.subst ![(Xv () : MvPowerSeries Unit ℂ_[p]), mulBy l ex (-1) (Xv ())]
        (0 : MvPowerSeries (Fin 2) ℂ_[p]) = 0 := by
      have := hsC 0 (Xv 0)
      simpa using this
    rw [(hr _ _ c0 c1).2.2.2.2, z] at H
    simp only [hsX, Matrix.cons_val_zero, Matrix.cons_val_one] at H
    exact H
  have P0 : Simeq (be l ex ph 0 0 : MvPowerSeries Unit ℂ_[p]) 0 := by
    have hs : ∀ i : Fin 2, MvPowerSeries.constantCoeff ((fun _ => (0 : MvPowerSeries Unit ℂ_[p])) i) = 0 :=
      fun _ => map_zero _
    have is : ∀ i : Fin 2, IntegralMv ((fun _ => (0 : MvPowerSeries Unit ℂ_[p])) i) := fun _ => int0
    have H := power_series_diagonal_linear p (Fin 2) Unit _ _ _ hs is hB
    obtain ⟨hsX, hsC, -, hr⟩ := OpsW.substOps_holds p l ex ph hex (hl0 hex hlex) (Fin 2) Unit _ hs
    have z : MvPowerSeries.subst (fun _ : Fin 2 => (0 : MvPowerSeries Unit ℂ_[p]))
        (0 : MvPowerSeries (Fin 2) ℂ_[p]) = 0 := by
      have := hsC 0 (Xv 0)
      simpa using this
    rw [(hr _ _ c0 c1).2.2.2.2, z, hsX, hsX] at H
    exact H
  have e0 : add l ex (Xv ()) (mulBy l ex (-1) (Xv ())) = (0 : MvPowerSeries Unit ℂ_[p]) := by
    have := addM hex hlex _ ccU 1 (-1)
    rw [mul1 hex hlex _ ccU, add_neg_cancel, mul0 hex hlex _ ccU] at this
    exact this
  have e00 : add l ex (0 : MvPowerSeries Unit ℂ_[p]) 0 = 0 := addZ hex hlex (0 : MvPowerSeries Unit ℂ_[p]) (map_zero _)
  have Q : Simeq (MvPowerSeries.C (zc 2) * phAt ph (Xv ()) : MvPowerSeries Unit ℂ_[p]) 0 := by
    have H := simeq_add (simeq_add P1 P0) hphi
    refine simeq_congr ?_ (simeq_symm H)
    simp only [be, e0, e00, zTwo, map_ofNat]
    ring
  exact Scale hZS zMul zOne _ 2 uTwo Q

end Steps

section Bridge

variable {p : ℕ} [Fact p.Prime] {σ : Type} (l ex ph : PowerSeries ℂ_[p])

theorem add_eq (a b : MvPowerSeries σ ℂ_[p]) : PI.SplitZeroG.add l ex a b = add l ex a b := rfl
theorem phAt_eq (a : MvPowerSeries σ ℂ_[p]) : PI.SplitZeroG.phAt ph a = phAt ph a := rfl
theorem be_eq (a b : MvPowerSeries σ ℂ_[p]) : PI.SplitZeroG.be l ex ph a b = be l ex ph a b := by
  simp only [PI.SplitZeroG.be, be, add_eq, phAt_eq]

end Bridge

theorem splitZeroG_bd (hZS : ZpSimeq) (hZI : ZpInt) (hZC : ZcFacts) {p : ℕ} [Fact p.Prime]
    {l ex ph : PowerSeries ℂ_[p]} (hex : PowerSeries.constantCoeff ex = 0)
    (hlex : PowerSeries.subst ex l = PowerSeries.X) (hp2 : p ≠ 2)
    (hgrp : IntegralMv (add l ex (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]))
    (hbi : Simeq (be l ex ph (add l ex (Xv 0) (Xv 1)) (Xv 2) : MvPowerSeries (Fin 3) ℂ_[p])
      (be l ex ph (Xv 0) (Xv 2) + be l ex ph (Xv 1) (Xv 2)))
    (hphi : Simeq (phAt ph (mulBy l ex (-1) (Xv ())) : MvPowerSeries Unit ℂ_[p]) (phAt ph (Xv ())))
    (a b : ℤ_[p]) (hu : IsUnit (a - b))
    (hc : Simeq (be l ex ph (mulBy l ex (zc a) (Xv 0)) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p])
      (be l ex ph (Xv 0) (mulBy l ex (zc b) (Xv 1)))) :
    Simeq (be l ex ph (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) 0 ∧
      Simeq (phAt ph (Xv ()) : MvPowerSeries Unit ℂ_[p]) 0 := by
  have hB' := hB (ph := ph) hex hlex hZS hZC hp2 hgrp hbi a b hu hc
  exact ⟨hB', hPh (ph := ph) hex hlex hZS hZI hZC hp2 hgrp hB' hphi⟩

theorem splitZeroG_of (hZS : ZpSimeq) (hZI : ZpInt) (hZC : ZcFacts) : PI.SplitZeroG.SplitZeroG := by
  intro p _ l ex ph _ hex hlex _ S hp2 _ _ hgrp hconj hbi hphi hα
  obtain ⟨α, hαS, a, b, hab, hu⟩ := hα
  have hc : Simeq (be l ex ph (mulBy l ex (zc a) (Xv 0)) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p])
      (be l ex ph (Xv 0) (mulBy l ex (zc b) (Xv 1))) := by
    have h := hconj α hαS
    rw [hab] at h
    exact h
  exact splitZeroG_bd hZS hZI hZC hex hlex hp2 hgrp hbi hphi a b hu hc

end PI.SZGW
