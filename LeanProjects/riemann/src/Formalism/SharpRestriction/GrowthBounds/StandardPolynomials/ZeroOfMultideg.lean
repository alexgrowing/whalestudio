import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.SumMulLe

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

section Glue

variable {C0 Cde CE1 CE2 : ℝ} {X : Loc} [NeZero X.m] [Fact X.p.Prime] {O : Type} [CommRing O] [IsDomain O]
  [IsDiscreteValuationRing O] [Algebra (WF X.p X.n') O] {w : O} {mm : ℝ} {n : ℕ} {β : GlobalTheory X}
  {L : LvDat C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β}
  {G : ∀ j, MvPolynomial (Fin (2 * segS X.TT j + 1) × Fin X.m) (KK O)} {Std : MonH X}

theorem zero_of_multideg {l : X.TT × Bool} {M : MonH X} (h : multideg M l = 0) (c : Fin (X.m + 1)) : M (l, c) = 0 :=
  (Finset.sum_eq_zero_iff.1 h) c (Finset.mem_univ c)

theorem PreSys.core (D : Formalism.BasicNotions.D7) [CharZero (KK O)]
    (P : PreSys C0 CE1 CE2 X O w (mm + (n : ℝ) * ka1 X) β L G Std)
    (hT : TCoreBody C0 Cde CE1 CE2 X O mm n β L Std) (hG0 : ∀ j, G j ≠ 0)
    (hGY : ∀ j k, G j ∈ YCond (KK O) (r := X.m) (L.LL j) ((BDk C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β j).T.J k)
      ((BDk C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β j).T.thr k))
    (hcov : ∀ j, ∑ i, (if (L.LL j).vec i then 0 else 1) ≤ X.N1)
    (u : P.κ → ℕ) (hu : ∀ a, u a ≤ P.mult a) (M : MonH X) (e : ℕ) (he1 : 1 ≤ e) (hsum : ∑ a, u a ≤ e) (hen : e < n)
    (hdeg : ∀ l, multideg M l = ∑ a, u a * P.dg a l) (hnd : ndM X M ≤ ∑ a, u a * P.od a + e) :
    P.sgR * (∏ a, P.sg a ^ (P.mult a - u a)) * monomial M 1 ∈
      SSe C0 Cde CE1 CE2 X O mm n (ordFam C0 CE1 CE2 X β) e := by
  classical
  set uC : ∀ j, P.ιC j → ℕ := fun j a => u (Sum.inl ⟨j, a⟩) with huCdef
  set uH : ∀ j, Fin (BDk C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β j).T.t → ℕ := fun j i => u (Sum.inr (Sum.inl ⟨j, i⟩)) with huHdef
  set uM : P.ιM → ℕ := fun a => u (Sum.inr (Sum.inr a)) with huMdef
  have huC : ∀ j a, uC j a ≤ 1 := fun j a => hu (Sum.inl ⟨j, a⟩)
  have huM : ∀ a, uM a ≤ P.multM a := fun a => hu (Sum.inr (Sum.inr a))
  have hsum' : (∑ j, ∑ a, uC j a) + ((∑ j, ∑ i, uH j i) + ∑ a, uM a) ≤ e := by
    rw [← P.sum_κ u]; exact hsum
  set B : MonH X := (∑ j, ∑ a, (1 - uC j a) • P.pl j a) + ∑ a, (P.multM a - uM a) • P.aM a with hB
  set Brem : MonH X := (∑ j, ∑ a, uC j a • P.pl j a) + ∑ a, uM a • P.aM a with hBrem
  have key : P.sgR * (∏ a, P.sg a ^ (P.mult a - u a)) * monomial M 1 =
      (∏ j, L.head O j (fun i => L.lv j i - uH j i) (∏ a, P.Kc j a ^ (1 - uC j a))) * monomial (P.R + B + M) 1 := by
    rw [P.prod_κ]
    exact P.ident (fun j a => 1 - uC j a) (fun j i => L.lv j i - uH j i) (fun a => P.multM a - uM a) M
  have hSB : Std = (P.R + B) + Brem := by
    refine P.stdEq.trans ?_
    have h1 : (∑ j, ∑ a, P.pl j a) = (∑ j, ∑ a, (1 - uC j a) • P.pl j a) + ∑ j, ∑ a, uC j a • P.pl j a := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← add_smul, Nat.sub_add_cancel (huC j a), one_smul]
    have h2 : (∑ a, P.multM a • P.aM a) = (∑ a, (P.multM a - uM a) • P.aM a) + ∑ a, uM a • P.aM a := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← add_smul, Nat.sub_add_cancel (huM a)]
    rw [h1, h2, hB, hBrem]
    abel
  have hSv : ∀ v, Std v = (P.R + B) v + Brem v := fun v => by
    rw [← Finsupp.add_apply]; exact DFunLike.congr_fun hSB v
  have hAv : ∀ v, (P.R + B + M) v = (P.R + B) v + M v := fun v => Finsupp.add_apply _ _ v
  have hmdB : ∀ l, multideg Brem l = (∑ j, ∑ a, uC j a * multideg (P.pl j a) l) + ∑ a, uM a * multideg (P.aM a) l := by
    intro l
    have : (mdHom X l) Brem = (∑ j, ∑ a, uC j a * (mdHom X l) (P.pl j a)) + ∑ a, uM a * (mdHom X l) (P.aM a) := by
      rw [hBrem]
      simp only [map_add, map_sum, map_nsmul, smul_eq_mul]
    exact this
  rw [key]
  refine hT e he1 hen (fun j i => L.lv j i - uH j i) (fun j i => Nat.sub_le _ _)
    (fun j => ∏ a, P.Kc j a ^ (1 - uC j a)) (fun j i => ∑ a, (1 - uC j a) * P.dK j a i) ?_ ?_ ?_ ?_ (P.R + B + M) ?_ ?_ ?_ ?_ ?_
  · exact fun j => glIntProd _ _ fun a _ => glIntPow (P.KInt j a) _
  · exact fun j => chain_pol_prod (KK O) Finset.univ (fun a i => (1 - uC j a) * P.dK j a i) _
      fun a _ => chain_pol_pow (KK O) (P.KPol j a) _
  · intro j i
    rw [← P.dKsum j i]
    refine Finset.sum_le_sum fun a _ => ?_
    calc (1 - uC j a) * P.dK j a i ≤ 1 * P.dK j a i := Nat.mul_le_mul_right _ (Nat.sub_le 1 _)
      _ = P.dK j a i := one_mul _
  · intro j k
    have hprod : (∏ a, P.Kc j a ^ (1 - uC j a)) * (∏ a, P.Kc j a ^ uC j a) = G j := by
      rw [← Finset.prod_mul_distrib, ← P.Kprod j]
      refine Finset.prod_congr rfl fun a _ => ?_
      rw [← pow_add, Nat.sub_add_cancel (huC j a), pow_one]
    refine ycond_factor D (L.LL j) _ _ _ (∏ a, P.Kc j a ^ uC j a) (fun i => ∑ a, uC j a * P.dK j a i)
      (chain_pol_prod (KK O) Finset.univ (fun a i => uC j a * P.dK j a i) _
        fun a _ => chain_pol_pow (KK O) (P.KPol j a) _) ?_ ?_ (X.N1 * e) ?_
    · intro h0
      apply hG0 j
      rw [← hprod, h0, mul_zero]
    · rw [hprod]; exact hGY j k
    · have hCj : ∑ a, uC j a ≤ e := by
        have h1 : ∑ a, uC j a ≤ ∑ j, ∑ a, uC j a :=
          Finset.single_le_sum (f := fun j => ∑ a, uC j a) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
        omega
      calc ∑ i, (if (L.LL j).vec i then 0 else ∑ a, uC j a * P.dK j a i)
          ≤ ∑ i, (if (L.LL j).vec i then 0 else 1) * ∑ a, uC j a := by
            refine Finset.sum_le_sum fun i _ => ?_
            by_cases hv : (L.LL j).vec i = true
            · simp [hv]
            · simp only [hv, if_false, one_mul, Bool.false_eq_true]
              refine Finset.sum_le_sum fun a _ => ?_
              calc uC j a * P.dK j a i ≤ uC j a * 1 := Nat.mul_le_mul_left _ (P.digit_le_one j a i)
                _ = uC j a := mul_one _
        _ = (∑ i, (if (L.LL j).vec i then 0 else 1)) * ∑ a, uC j a := (Finset.sum_mul _ _ _).symm
        _ ≤ X.N1 * e := Nat.mul_le_mul (hcov j) hCj
  · intro l
    calc ∑ c, (Std (l, c) - (P.R + B + M) (l, c)) ≤ ∑ c, Brem (l, c) := by
          refine Finset.sum_le_sum fun c _ => ?_
          rw [hSv, hAv]; omega
      _ = multideg Brem l := rfl
      _ = (∑ j, ∑ a, uC j a * multideg (P.pl j a) l) + ∑ a, uM a * multideg (P.aM a) l := hmdB l
      _ ≤ (∑ j, ∑ a, uC j a) * X.p ^ X.G' + (∑ a, uM a) * X.p ^ X.G' := by
          refine Nat.add_le_add ?_ (sum_mul_le _ _ _ fun a => by rw [P.polM a l]; exact P.dgMQ a l)
          rw [Finset.sum_mul]
          exact Finset.sum_le_sum fun j _ => sum_mul_le _ _ _ fun a => P.plQ j a l
      _ = ((∑ j, ∑ a, uC j a) + ∑ a, uM a) * X.p ^ X.G' := (Nat.add_mul _ _ _).symm
      _ ≤ e * X.p ^ X.G' := Nat.mul_le_mul_right _ (by omega)
      _ = X.p ^ X.G' * e := Nat.mul_comm _ _
  · intro l
    calc ∑ c, ((P.R + B + M) (l, c) - Std (l, c)) ≤ ∑ c, M (l, c) := by
          refine Finset.sum_le_sum fun c _ => ?_
          rw [hSv, hAv]; omega
      _ = multideg M l := rfl
      _ = ∑ a, u a * P.dg a l := hdeg l
      _ ≤ (∑ a, u a) * X.p ^ X.G' := sum_mul_le _ _ _ fun a => P.dgQ a l
      _ ≤ e * X.p ^ X.G' := Nat.mul_le_mul_right _ hsum
      _ = X.p ^ X.G' * e := Nat.mul_comm _ _
  · intro j c
    have hM0 : multideg M (topEnd X j, false) = 0 := by
      rw [hdeg]
      exact Finset.sum_eq_zero fun a _ => by rw [P.dgY a j, mul_zero]
    have hB0 : multideg Brem (topEnd X j, false) = 0 := by
      rw [hmdB]
      have h1 : (∑ j', ∑ a, uC j' a * multideg (P.pl j' a) (topEnd X j, false)) = 0 :=
        Finset.sum_eq_zero fun j' _ => Finset.sum_eq_zero fun a _ => by rw [P.plY j' a j, mul_zero]
      have h2 : (∑ a, uM a * multideg (P.aM a) (topEnd X j, false)) = 0 :=
        Finset.sum_eq_zero fun a _ => by rw [P.polM a, P.dgMY a j, mul_zero]
      rw [h1, h2]
    rw [hSv, hAv, zero_of_multideg hM0 c, zero_of_multideg hB0 c]
  · rw [← key]
    refine mem_Pol_iffW.2 fun l => ?_
    have h1 := hom_total (mdHom X l) P.sg (fun a => P.dg a l) (fun a => mem_Pol_iffW.1 (P.sgMd a) l)
      (mem_Pol_iffW.1 P.rigPol l) P.mult u M
    have h2 : P.dR l + ∑ a, (P.mult a - u a) * P.dg a l + (mdHom X l) M = hhDegs X.TT X.aT X.bT l := by
      have h3 : (mdHom X l) M = ∑ a, u a * P.dg a l := hdeg l
      rw [h3, add_assoc, sum_split _ _ _ hu, P.degκ l]
    rw [h2] at h1
    exact h1
  · rw [← key]
    intro m hm
    have h1 := hom_total (ndHom X) P.sg P.od P.sgNd P.rigHom P.mult u M m hm
    have h1' : ndM X m = P.oR + ∑ a, (P.mult a - u a) * P.od a + ndM X M := h1
    have h2 := sum_split P.mult u P.od hu
    have h3 := P.ordκ
    omega

def PreSys.toFacSys (D : Formalism.BasicNotions.D7) [CharZero (KK O)]
    (P : PreSys C0 CE1 CE2 X O w (mm + (n : ℝ) * ka1 X) β L G Std)
    (hStd : (monomial Std (1 : KK O) : RHH O X) = ∏ j, L.stdPoly O j)
    (hT : TCoreBody C0 Cde CE1 CE2 X O mm n β L Std) (hG0 : ∀ j, G j ≠ 0)
    (hGY : ∀ j k, G j ∈ YCond (KK O) (r := X.m) (L.LL j) ((BDk C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β j).T.J k)
      ((BDk C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β j).T.thr k))
    (hcov : ∀ j, ∑ i, (if (L.LL j).vec i then 0 else 1) ≤ X.N1) :
    FacSys C0 Cde CE1 CE2 X O w mm n (ordFam C0 CE1 CE2 X β)
      (symFam (KK O) X.p C0 CE1 CE2 X β (fun j => L.word O j (G j))) where
  κ := P.κ
  fin := inferInstance
  mult := P.mult
  f := P.f
  sg := P.sg
  od := P.od
  dg := P.dg
  fR := P.fR
  sgR := P.sgR
  oR := P.oR
  fac := by
    rintro (⟨j, a⟩ | ⟨j, i⟩ | a)
    · exact P.facC j a
    · exact P.facH j i
    · exact P.facM a
  sgHom := fun a m hm => P.sgNd a m hm
  liftPol := by
    rintro (⟨j, a⟩ | ⟨j, i⟩ | a)
    · exact P.liftC j a
    · exact P.liftH j i
    · exact P.liftM a
  sgPol := P.sgMd
  rigA := P.rigA
  rigLift := P.rigLift
  rigInt := P.rigInt
  clean := fun g' hg' hne => by rw [P.fprod]; exact P.clean g' hg' hne
  total := by rw [P.fprod]; exact P.total
  ordEq := P.ordκ
  symEq := P.symκ hStd
  core := fun u hu M e he1 hsum hen hdeg hnd => P.core D hT hG0 hGY hcov u hu M e he1 hsum hen hdeg hnd

end Glue

end Formalism.MainNotions.ColumnSystems.Pf
