import Formalism.LocalToGlobal.CharacterGerms.ConstantZeroRestrictPoints

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds.FunEq

open Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.PartialDerivEval ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ MvPowerSeries

variable {C : Type} [Field C] [CharZero C] {dd : ℕ} {V : VF C}

def ix (i : Fin dd) (L : ℕ) (γ : Fin 2 × Fin dd →₀ ℕ) : Fin 3 × Fin dd →₀ ℕ :=
  Finsupp.single ((0 : Fin 3), i) L + γ.mapDomain (up 2)

theorem index_raise_first (i : Fin dd) (L : ℕ) (γ : Fin 2 × Fin dd →₀ ℕ) (j : Fin dd) :
    ix i L γ ((0 : Fin 3), j) = if j = i then L else 0 := by
  have hn : ((0 : Fin 3), j) ∉ Set.range (up (dd := dd) 2) := by
    rintro ⟨q, hq⟩
    simp only [up, Prod.mk.injEq] at hq
    exact Fin.succ_ne_zero _ hq.1
  simp only [ix, Finsupp.add_apply, Finsupp.mapDomain_notin_range _ _ hn, add_zero, Finsupp.single_apply,
    Prod.mk.injEq, true_and]
  by_cases h : j = i
  · subst h; simp
  · simp [h, Ne.symm h]

def FrobX (V : VF C) (f : PS C 3 dd) : Prop :=
  ∀ p : Fin 3 × Fin dd →₀ ℕ, (∃ j, ¬ V.l ∣ p ((0 : Fin 3), j)) → V.MM (coeff p f)

def FrobD (V : VF C) (f : PS C 3 dd) : Prop := ∀ j : Fin dd, MaximalIdealCongruence.MMS V (pderiv C ((0 : Fin 3), j) f)

private theorem v_natCast_nonneg_of_vf (V : VF C) (m : ℕ) : 0 ≤ V.v (m : C) := by
  induction m with
  | zero => simp [AddValuation.map_zero]
  | succ m ih =>
    rw [Nat.cast_succ]
    refine le_trans (le_min ih ?_) (AddValuation.map_add _ _ _)
    rw [AddValuation.map_one]

private theorem v_intCast_nonneg' (V : VF C) (a : ℤ) : 0 ≤ V.v (a : C) := by
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg a
  · rw [Int.cast_natCast]
    exact v_natCast_nonneg_of_vf V m
  · rw [Int.cast_neg, Int.cast_natCast, AddValuation.map_neg]
    exact v_natCast_nonneg_of_vf V m

private theorem v_natCast_nonpos_of_not_dvd (V : VF C) (n : ℕ) (hn : ¬ V.l ∣ n) : V.v (n : C) ≤ 0 := by
  by_contra hlt
  push_neg at hlt
  have hcop : Nat.Coprime n V.l :=
    Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd V.l_prime).mpr hn)
  have hb := Nat.gcd_eq_gcd_ab n V.l
  rw [hcop.gcd_eq_one, Nat.cast_one] at hb
  have h1 : (1 : C) = (n : C) * (Nat.gcdA n V.l : C) + (V.l : C) * (Nat.gcdB n V.l : C) := by
    have := congrArg (fun z : ℤ => (z : C)) hb
    exact_mod_cast this
  have h01 : (0 : WithTop ℝ) < 1 := by
    rw [← WithTop.coe_zero, ← WithTop.coe_one, WithTop.coe_lt_coe]
    exact one_pos
  have ha : 0 < V.v ((n : C) * (Nat.gcdA n V.l : C)) := by
    rw [AddValuation.map_mul]
    exact add_pos_of_pos_of_nonneg hlt (v_intCast_nonneg' V _)
  have hb' : 0 < V.v ((V.l : C) * (Nat.gcdB n V.l : C)) := by
    rw [AddValuation.map_mul, V.v_l]
    exact add_pos_of_pos_of_nonneg h01 (v_intCast_nonneg' V _)
  have := lt_of_lt_of_le (lt_min ha hb') (AddValuation.map_add _ _ _)
  rw [← h1, AddValuation.map_one] at this
  exact lt_irrefl _ this

theorem frobX_of {f : PS C 3 dd} (hi : IntS V f) (hd : FrobD V f) : FrobX V f := by
  unfold FrobD MaximalIdealCongruence.MMS at hd
  rintro p ⟨j, hj⟩
  have hp0 : p ((0 : Fin 3), j) ≠ 0 := by
    intro h
    rw [h] at hj
    exact hj (dvd_zero _)
  have h := hd j (p - Finsupp.single ((0 : Fin 3), j) 1)
  have hle : Finsupp.single ((0 : Fin 3), j) 1 ≤ p := by
    rw [Finsupp.single_le_iff]
    exact Nat.one_le_iff_ne_zero.mpr hp0
  rw [MvPowerSeries.coeff_pderiv, tsub_add_cancel_of_le hle] at h
  have hn : ((((p - Finsupp.single ((0 : Fin 3), j) 1 : Fin 3 × Fin dd →₀ ℕ) ((0 : Fin 3), j)) : ℕ) : C) + 1 =
      (p ((0 : Fin 3), j) : C) := by
    rw [Finsupp.tsub_apply, Finsupp.single_eq_same]
    exact_mod_cast Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hp0)
  rw [hn] at h
  unfold VF.MM at h ⊢
  rw [AddValuation.map_mul] at h
  by_contra hc
  push_neg at hc
  have := add_le_add hc (v_natCast_nonpos_of_not_dvd V _ hj)
  rw [add_zero] at this
  exact absurd h (not_lt.mpr this)

private theorem mm_add_of_mm_of_mm {V : VF C} {a b : C} (ha : V.MM a) (hb : V.MM b) : V.MM (a + b) := by
  unfold VF.MM at *
  exact lt_of_lt_of_le (lt_min ha hb) (AddValuation.map_add _ _ _)

private theorem mm_finset_sum_of_forall_mm {V : VF C} {ι : Type} (s : Finset ι) (a : ι → C) (h : ∀ i ∈ s, V.MM (a i)) :
    V.MM (∑ i ∈ s, a i) := by
  refine Finset.sum_induction a (fun x => V.MM x) (fun x y hx hy => mm_add_of_mm_of_mm hx hy) ?_ h
  unfold VF.MM
  rw [AddValuation.map_zero, ← WithTop.coe_zero]
  exact WithTop.coe_lt_top _

private theorem mms_mul_of_intS_of_mms {V : VF C} {σ : Type} {f h : MvPowerSeries σ C} (hf : IntS V f)
    (hh : MaximalIdealCongruence.MMS V h) : MaximalIdealCongruence.MMS V (f * h) := by
  intro μ
  rw [MvPowerSeries.coeff_mul]
  apply mm_finset_sum_of_forall_mm
  intro x _
  have h1 := hf x.1
  have h2 := hh x.2
  unfold VF.Ge at h1
  unfold VF.MM at h2 ⊢
  rw [AddValuation.map_mul]
  have h1' : (0 : WithTop ℝ) ≤ V.v (coeff x.1 f) := by simpa using h1
  exact lt_of_lt_of_le h2 (le_add_of_nonneg_left h1')

theorem frobD_mul {f g : PS C 3 dd} (hf : IntS V f) (hg : IntS V g) (hf' : FrobD V f) (hg' : FrobD V g) :
    FrobD V (f * g) := by
  intro j
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  intro μ
  rw [map_add]
  apply mm_add_of_mm_of_mm
  · exact mms_mul_of_intS_of_mms hf (hg' j) μ
  · exact mms_mul_of_intS_of_mms hg (hf' j) μ

theorem eq_up_of {p : Fin 3 × Fin dd →₀ ℕ} (hp : ∀ j, p ((0 : Fin 3), j) = 0) :
    (Finsupp.comapDomain (up 2) p ((up_inj 2).injOn)).mapDomain (up 2) = p := by
  ext ⟨k, j⟩
  induction k using Fin.cases with
  | zero =>
    rw [Finsupp.mapDomain_notin_range, hp]
    rintro ⟨q, hq⟩
    simp only [up, Prod.mk.injEq] at hq
    exact Fin.succ_ne_zero _ hq.1
  | succ k' =>
    have e : ((Fin.succ k', j) : Fin 3 × Fin dd) = up 2 (k', j) := rfl
    rw [e, Finsupp.mapDomain_apply (up_inj 2), Finsupp.comapDomain_apply]

theorem coeff_free {f : PS C 3 dd} (h1 : ev (rz 2) f = 1) {p : Fin 3 × Fin dd →₀ ℕ}
    (hp : ∀ j, p ((0 : Fin 3), j) = 0) : coeff p f = if p = 0 then 1 else 0 := by
  classical
  have hs : MvPowerSeries.HasSubst (fun q : Fin 3 × Fin dd => rz (C := C) (dd := dd) 2 q.1 q.2) := by
    have hz : ∀ q : Fin 3 × Fin dd, constantCoeff (rz (C := C) (dd := dd) 2 q.1 q.2) = 0 := by
      rintro ⟨k, i⟩
      induction k using Fin.cases <;> simp [rz, pt]
    first
    | exact MvPowerSeries.hasSubst_of_constantCoeff_zero hz
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero' hz
    | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun q => by rw [hz q]; exact IsNilpotent.zero)
    | exact MvPowerSeries.hasSubst_of_constantCoeff_nilpotent (fun q => by rw [hz q]; exact IsNilpotent.zero)
  have hmon : ∀ d' : Fin 2 × Fin dd →₀ ℕ,
      (d'.prod fun s n => (X s : PS C 2 dd) ^ n) = MvPowerSeries.monomial d' (1 : C) := by
    intro d'
    induction d' using Finsupp.induction with
    | zero => rw [Finsupp.prod_zero_index, MvPowerSeries.monomial_zero_one]
    | single_add a b g _ _ ih =>
      rw [Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _), ih,
        Finsupp.prod_single_index (h := fun x n => (X x : PS C 2 dd) ^ n) (pow_zero _), MvPowerSeries.X_pow_eq, MvPowerSeries.monomial_mul_monomial,
        one_mul]
  have inj : Function.Injective (Finsupp.mapDomain (M := ℕ) (up (dd := dd) 2)) :=
    Finsupp.mapDomain_injective (up_inj 2)
  have hprod : ∀ (d : Fin 3 × Fin dd →₀ ℕ) (e : Fin 2 × Fin dd →₀ ℕ),
      coeff e (d.prod fun s n => (fun q : Fin 3 × Fin dd => rz (C := C) (dd := dd) 2 q.1 q.2) s ^ n) =
        if d = e.mapDomain (up 2) then 1 else 0 := by
    intro d e
    by_cases hx : ∀ j, d ((0 : Fin 3), j) = 0
    · have hd := (eq_up_of hx).symm
      rw [hd, Finsupp.prod_mapDomain_index (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
      show coeff e ((Finsupp.comapDomain (up 2) d ((up_inj 2).injOn)).prod
        fun s n => (X s : PS C 2 dd) ^ n) = _
      rw [hmon, MvPowerSeries.coeff_monomial]
      by_cases he : e = Finsupp.comapDomain (up 2) d ((up_inj 2).injOn)
      · rw [if_pos he, if_pos (by rw [he])]
      · rw [if_neg he, if_neg (fun h => he (inj h).symm)]
    · push_neg at hx
      obtain ⟨j, hj⟩ := hx
      have h0 : (d.prod fun s n => (fun q : Fin 3 × Fin dd => rz (C := C) (dd := dd) 2 q.1 q.2) s ^ n) = 0 := by
        apply Finset.prod_eq_zero (i := ((0 : Fin 3), j))
        · exact Finsupp.mem_support_iff.mpr hj
        · show (rz (C := C) (dd := dd) 2 0 j) ^ (d ((0 : Fin 3), j)) = 0
          rw [show rz (C := C) (dd := dd) 2 0 j = 0 from rfl, zero_pow hj]
      rw [h0, map_zero, if_neg]
      intro h
      apply hj
      rw [h, Finsupp.mapDomain_notin_range]
      rintro ⟨q, hq⟩
      simp only [up, Prod.mk.injEq] at hq
      exact Fin.succ_ne_zero _ hq.1
  have key : ∀ e : Fin 2 × Fin dd →₀ ℕ,
      coeff e (ev (rz (C := C) (dd := dd) 2) f) = coeff (e.mapDomain (up 2)) f := by
    intro e
    show coeff e (MvPowerSeries.subst (fun q : Fin 3 × Fin dd => rz (C := C) (dd := dd) 2 q.1 q.2) f) = _
    rw [MvPowerSeries.coeff_subst hs, finsum_eq_single _ (e.mapDomain (up 2))]
    · rw [hprod, if_pos rfl, smul_eq_mul, mul_one]
    · intro d hd
      rw [hprod, if_neg hd, smul_zero]
  have h2 := key (Finsupp.comapDomain (up 2) p ((up_inj 2).injOn))
  rw [h1, eq_up_of hp, MvPowerSeries.coeff_one] at h2
  rw [← h2]
  by_cases hp0 : p = 0
  · subst hp0
    rw [if_pos rfl, if_pos]
    ext s
    rfl
  · rw [if_neg hp0, if_neg]
    intro h
    apply hp0
    rw [← eq_up_of hp, h, Finsupp.mapDomain_zero]

theorem x_le (i : Fin dd) (γ : Fin 2 × Fin dd →₀ ℕ) {p : Fin 3 × Fin dd →₀ ℕ} (hp : p ≤ ix i V.l γ)
    (j : Fin dd) (hj : j ≠ i) : p ((0 : Fin 3), j) = 0 := by
  have h := hp ((0 : Fin 3), j)
  rw [index_raise_first, if_neg hj] at h
  exact Nat.le_zero.mp h

private theorem mm_zero' : V.MM (0 : C) := by
  unfold VF.MM
  rw [AddValuation.map_zero, ← WithTop.coe_zero]
  exact WithTop.coe_lt_top _

private theorem mm_mul_of_mm_of_ge_zero {a b : C} (ha : V.MM a) (hb : V.Ge 0 b) : V.MM (a * b) := by
  unfold VF.MM at *
  unfold VF.Ge at hb
  rw [AddValuation.map_mul]
  have hb' : (0 : WithTop ℝ) ≤ V.v b := by simpa using hb
  exact lt_of_lt_of_le ha (le_add_of_nonneg_right hb')

theorem coeff_mul_cong {f g : PS C 3 dd} (hf : IntS V f) (hg : IntS V g) (hfF : FrobX V f) (hgF : FrobX V g)
    (hf1 : ev (rz 2) f = 1) (hg1 : ev (rz 2) g = 1) (i : Fin dd) (γ : Fin 2 × Fin dd →₀ ℕ) :
    V.MM (coeff (ix i V.l γ) (f * g) - coeff (ix i V.l γ) f - coeff (ix i V.l γ) g) := by
  classical
  unfold FrobX at hfF hgF
  set N := ix i V.l γ with hN
  have hN0 : N ≠ 0 := by
    intro h
    have h2 := congrArg (fun p => p ((0 : Fin 3), i)) h
    simp [hN, index_raise_first] at h2
    exact V.l_prime.ne_zero h2
  have hf0 : coeff 0 f = 1 := by
    have := coeff_free hf1 (p := 0) (fun j => rfl)
    simpa using this
  have hg0 : coeff 0 g = 1 := by
    have := coeff_free hg1 (p := 0) (fun j => rfl)
    simpa using this
  rw [MvPowerSeries.coeff_mul]
  have h1 : ((0 : Fin 3 × Fin dd →₀ ℕ), N) ∈ Finset.HasAntidiagonal.antidiagonal N := by
    rw [Finset.HasAntidiagonal.mem_antidiagonal]
    simp
  have h2 : (N, (0 : Fin 3 × Fin dd →₀ ℕ)) ∈ (Finset.HasAntidiagonal.antidiagonal N).erase (0, N) := by
    rw [Finset.mem_erase]
    refine ⟨fun h => hN0 (congrArg Prod.fst h), ?_⟩
    rw [Finset.HasAntidiagonal.mem_antidiagonal]
    simp
  rw [← Finset.add_sum_erase _ _ h1, ← Finset.add_sum_erase _ _ h2]
  dsimp only
  rw [hf0, hg0, one_mul, mul_one]
  have e : ∀ A B S : C, A + (B + S) - B - A = S := by
    intros
    ring
  rw [e]
  apply mm_finset_sum_of_forall_mm
  intro x hx
  obtain ⟨hne2, hx'⟩ := Finset.mem_erase.mp hx
  obtain ⟨hne1, hx''⟩ := Finset.mem_erase.mp hx'
  have hsum := Finset.HasAntidiagonal.mem_antidiagonal.mp hx''
  have ha : x.1 ≤ N := by
    rw [← hsum]
    exact le_self_add
  have hb : x.2 ≤ N := by
    rw [← hsum]
    exact le_add_self
  have ha0 : x.1 ≠ 0 := by
    intro h
    apply hne1
    refine Prod.ext h ?_
    show x.2 = N
    rw [← hsum, h, zero_add]
  have hb0 : x.2 ≠ 0 := by
    intro h
    apply hne2
    refine Prod.ext ?_ h
    show x.1 = N
    rw [← hsum, h, add_zero]
  have hxa : ∀ j, j ≠ i → x.1 ((0 : Fin 3), j) = 0 := fun j hj => x_le i γ ha j hj
  have hxb : ∀ j, j ≠ i → x.2 ((0 : Fin 3), j) = 0 := fun j hj => x_le i γ hb j hj
  have hti : x.1 ((0 : Fin 3), i) + x.2 ((0 : Fin 3), i) = V.l := by
    have h3 := congrArg (fun p => p ((0 : Fin 3), i)) hsum
    simp only [Finsupp.add_apply] at h3
    rw [h3, hN, index_raise_first, if_pos rfl]
  by_cases hd : V.l ∣ x.1 ((0 : Fin 3), i)
  · obtain ⟨q, hq⟩ := hd
    rcases q with _ | _ | q
    · have hfree : ∀ j, x.1 ((0 : Fin 3), j) = 0 := by
        intro j
        by_cases hj : j = i
        · rw [hj]
          simpa using hq
        · exact hxa j hj
      rw [coeff_free hf1 hfree, if_neg ha0, zero_mul]
      exact mm_zero'
    · have hfree : ∀ j, x.2 ((0 : Fin 3), j) = 0 := by
        intro j
        by_cases hj : j = i
        · rw [hj]
          simp at hq
          omega
        · exact hxb j hj
      rw [coeff_free hg1 hfree, if_neg hb0, mul_zero]
      exact mm_zero'
    · exfalso
      nlinarith [V.l_prime.pos]
  · exact mm_mul_of_mm_of_ge_zero (hfF x.1 ⟨i, hd⟩) (hg x.2)

end Formalism.L2.FormalSeriesBounds.FunEq
