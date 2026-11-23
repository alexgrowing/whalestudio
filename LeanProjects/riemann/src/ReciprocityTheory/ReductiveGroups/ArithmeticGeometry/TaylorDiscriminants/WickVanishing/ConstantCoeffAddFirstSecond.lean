import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.IntegralFamilyPointZero

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB.LogPf

namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab

section Gen

variable {k : Type} [CommRing k] {d : ℕ}

theorem cc_pderiv' {n : ℕ} (f : PS k n d) (v : Fin n × Fin d) :
    constantCoeff (pderiv k v f) = coeff (Finsupp.single v 1) f := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_pderiv]
  simp

theorem zero_constant_first_point : CZ (![pt k (n := 2) d 0] : Fin 1 → Pt k 2 d) := fun j i => by simp [pt]

theorem zp (h : PS k 2 d) (i : Fin d) (p : Pt k 3 d) (hp : ∀ c, constantCoeff (p c) = 0)
    (hpz : ∀ c, pderiv k ((2 : Fin 3), i) (p c) = 0) :
    ev (n := 2) ![pt k d 0, pt k d 1, 0] (pderiv k ((2 : Fin 3), i) (ev (n := 3) ![p, pt k d 2] h)) =
      -ev (n := 2) ![fun c => ev (n := 2) ![pt k d 0, pt k d 1, 0] (p c)]
        (-ev (n := 1) ![pt k d 0, 0] (pderiv k ((1 : Fin 2), i) h)) := by
  have hq : CZ (![p, pt k d 2] : Fin 2 → Pt k 3 d) := CZ.cons hp (CZ.cons (cc_pt 2) CZ.nil)
  have hp' : CZ (![fun c => ev (n := 2) ![pt k d 0, pt k d 1, 0] (p c)] : Fin 1 → Pt k 2 d) :=
    CZ.cons (fun c => constantCoeff_ev czZ (hp c)) CZ.nil
  rw [pderiv_ev hq, Fintype.sum_prod_type, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hpz, mul_zero, Finset.sum_const_zero,
    zero_add, pderiv_pt, Prod.mk.injEq, true_and, mul_ite, mul_one, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  rw [ev_neg hp', neg_neg, ev_ev czZ hq, ev_ev hp' cz1]
  congr 1
  funext j c
  fin_cases j
  · simp [pt_apply, ev_X hp']
  · simp [pt_apply, ev_X czZ, ev_zero' hp']

end Gen

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k]

theorem lawK_F (B : FB R d O) : (lawK k B).F = B.FK k := rfl

theorem cc_h {B : FB R d O} {h : PS k 2 d} (hc : B.IsCanonGauge k h) : constantCoeff h = 0 := by
  have h0 := congrArg constantCoeff hc.ax0
  rw [cc_ev' (by intro j i; fin_cases j <;> simp [pt]), map_zero] at h0
  exact h0

theorem constantCoeff_first_factor (B : FB R d O) : constantCoeff B.ph1 = 1 := by
  have h := congrArg constantCoeff B.cocycleLeft_zero_fst
  rw [cc_ev' (by intro j i; fin_cases j <;> simp [pt]), map_one] at h
  exact h

theorem constantCoeff_add_first_second (B : FB R d O) (l : Fin d) :
    constantCoeff (addOf (B.FK k) (pt k (n := 3) d 0) (pt k d 1) l) = 0 := by
  unfold addOf
  rw [cc_ev' (by intro j i; fin_cases j <;> simp [pt])]
  show constantCoeff (MvPowerSeries.map (algebraMap R k) (B.G.F l)) = 0
  rw [MvPowerSeries.constantCoeff_map, B.G.const l, map_zero]

theorem sig_add {B : FB R d O} {h : PS k 2 d} (hc : B.IsCanonGauge k h) (i : Fin d) :
    ev (n := 2) ![(lawK k B).F] (sgOf k h i) - ev (n := 2) ![pt k d 0] (sgOf k h i) -
      ev (n := 2) ![pt k d 1] (sgOf k h i) ∈ Ig R k (Fin 2 × Fin d) := by
  have c02 : CZ (![pt k (n := 3) d 0, pt k d 2] : Fin 2 → Pt k 3 d) := CZ.cons (cc_pt 0) (CZ.cons (cc_pt 2) CZ.nil)
  have c12 : CZ (![pt k (n := 3) d 1, pt k d 2] : Fin 2 → Pt k 3 d) := CZ.cons (cc_pt 1) (CZ.cons (cc_pt 2) CZ.nil)
  have cA : CZ (![addOf (B.FK k) (pt k (n := 3) d 0) (pt k d 1), pt k d 2] : Fin 2 → Pt k 3 d) :=
    CZ.cons (constantCoeff_add_first_second B) (CZ.cons (cc_pt 2) CZ.nil)
  have hH0 : constantCoeff (ev (n := 3) ![pt k d 0, pt k d 2] h + ev (n := 3) ![pt k d 1, pt k d 2] h -
      ev (n := 3) ![addOf (B.FK k) (pt k d 0) (pt k d 1), pt k d 2] h) = 0 := by
    rw [map_sub, map_add, cc_ev' c02, cc_ev' c12, cc_ev' cA, cc_h hc]
    simp
  have hH := ig_dlog B.ph1 (constantCoeff_first_factor B) _ hH0 hc.ph1 ((2 : Fin 3), i)
  have h2 := ig_ev czZ integral_family_pair_zero hH
  have z0 : ∀ c, pderiv k ((2 : Fin 3), i) (pt k (n := 3) d 0 c) = 0 := fun c => by simp [pderiv_pt]
  have z1 : ∀ c, pderiv k ((2 : Fin 3), i) (pt k (n := 3) d 1 c) = 0 := fun c => by simp [pderiv_pt]
  have zA : ∀ c, pderiv k ((2 : Fin 3), i) (addOf (B.FK k) (pt k (n := 3) d 0) (pt k d 1) c) = 0 := fun c =>
    pderiv_ev_zero cz01 _ _ (fun j l => by fin_cases j <;> simp [pderiv_pt])
  rw [map_sub, map_add, ev_sub czZ, ev_add czZ, zp h i _ (cc_pt 0) z0, zp h i _ (cc_pt 1) z1,
    zp h i _ (constantCoeff_add_first_second B) zA] at h2
  have f0 : (fun c => ev (n := 2) ![pt k d 0, pt k d 1, 0] (pt k (n := 3) d 0 c)) = pt k (n := 2) d 0 := by
    funext c; simp [pt_apply, ev_X czZ]
  have f1 : (fun c => ev (n := 2) ![pt k d 0, pt k d 1, 0] (pt k (n := 3) d 1 c)) = pt k (n := 2) d 1 := by
    funext c; simp [pt_apply, ev_X czZ]
  have fA : (fun c => ev (n := 2) ![pt k d 0, pt k d 1, 0] (addOf (B.FK k) (pt k (n := 3) d 0) (pt k d 1) c)) =
      (lawK k B).F := by
    funext c
    show ev (n := 2) ![pt k d 0, pt k d 1, 0] (ev (n := 3) ![pt k d 0, pt k d 1] (B.FK k c)) = B.FK k c
    rw [ev_ev czZ cz01]
    have : (fun j c => ev (n := 2) ![pt k d 0, pt k d 1, 0] ((![pt k (n := 3) d 0, pt k d 1] : Fin 2 → Pt k 3 d) j c)) =
        fun j => pt k (n := 2) d j := by
      funext j c; fin_cases j <;> simp [pt_apply, ev_X czZ]
    rw [this, ev_pt]
  have es : -ev (n := 1) ![pt k d 0, 0] (pderiv k ((1 : Fin 2), i) h) = sgOf k h i := rfl
  rw [f0, f1, fA, es] at h2
  have e : ev (n := 2) ![(lawK k B).F] (sgOf k h i) - ev (n := 2) ![pt k d 0] (sgOf k h i) -
      ev (n := 2) ![pt k d 1] (sgOf k h i) =
      -ev (n := 2) ![pt k d 0] (sgOf k h i) + -ev (n := 2) ![pt k d 1] (sgOf k h i) -
        -ev (n := 2) ![(lawK k B).F] (sgOf k h i) := by ring
  rw [e]
  exact h2

theorem sig_lin {B : FB R d O} {h : PS k 2 d} (hc : B.IsCanonGauge k h) (i b : Fin d) :
    ∑ c, pderiv k ((0 : Fin 1), c) (sgOf k h i) * Jac (lawK k B) c b - C (sg1 k h i b) ∈ Ig R k (Fin 1 × Fin d) := by
  have h3 := ig_ev cz1 integral_family_point_zero (ig_pderiv (sig_add hc i) ((1 : Fin 2), b))
  have d0 : pderiv k ((1 : Fin 2), b) (ev (n := 2) ![pt k d 0] (sgOf k h i)) = 0 :=
    pderiv_ev_zero zero_constant_first_point _ _ (fun j l => by fin_cases j; simp [pderiv_pt])
  rw [map_sub, map_sub, d0, sub_zero, ev_sub cz1, d_F, d_y, ez_y, ev_sum cz1] at h3
  simp only [ev_mul cz1, ezF, ez_dF, cc_pderiv'] at h3
  exact h3

theorem dof_sig {B : FB R d O} {h : PS k 2 d} (hc : B.IsCanonGauge k h) (u : Fin d → R) (i : Fin d) :
    Dof (B.FK k) (fun j => algebraMap R k (u j)) (sgOf k h i) -
      C (∑ j, sg1 k h i j * algebraMap R k (u j)) ∈ Ig R k (Fin 1 × Fin d) := by
  have e1 : Dof (B.FK k) (fun j => algebraMap R k (u j)) (sgOf k h i) =
      ∑ b, C (algebraMap R k (u b)) * ∑ c, pderiv k ((0 : Fin 1), c) (sgOf k h i) * Jac (lawK k B) c b := by
    simp only [Dof, Jac, lawK_F, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => by ring
  have e2 : (C (∑ j, sg1 k h i j * algebraMap R k (u j)) : PS k 1 d) =
      ∑ b, C (algebraMap R k (u b)) * C (sg1 k h i b) := by
    simp only [map_sum, map_mul]
    exact Finset.sum_congr rfl fun b _ => mul_comm _ _
  rw [e1, e2, ← Finset.sum_sub_distrib]
  refine sum_mem fun b _ => ?_
  rw [← mul_sub]
  exact mul_mem (ig_C _) (sig_lin hc i b)

end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
