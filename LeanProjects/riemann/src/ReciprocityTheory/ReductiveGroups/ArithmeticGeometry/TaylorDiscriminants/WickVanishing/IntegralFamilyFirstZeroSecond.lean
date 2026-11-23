import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.ConstantCoeffAddFirstSecond

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB.LogPf

namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab

section Gen

variable {k : Type} [CommRing k] {d : ℕ}

theorem d2 {n : ℕ} {p q : Pt k n d} (hpq : CZ (![p, q] : Fin 2 → Pt k n d)) (h : PS k 2 d) (v : Fin n × Fin d) :
    pderiv k v (ev (n := n) ![p, q] h) = ∑ c, ev (n := n) ![p, q] (pderiv k ((0 : Fin 2), c) h) * pderiv k v (p c) +
      ∑ c, ev (n := n) ![p, q] (pderiv k ((1 : Fin 2), c) h) * pderiv k v (q c) := by
  rw [pderiv_ev hpq, Fintype.sum_prod_type, Fin.sum_univ_two]
  rfl

theorem cz0z : CZ (![pt k (n := 2) d 0, 0, pt k d 1] : Fin 3 → Pt k 2 d) := by
  intro j i
  fin_cases j <;> simp [cc_pt, cc_zero]

theorem zero_constant_zero_second : CZ (![0, pt k (n := 2) d 1] : Fin 2 → Pt k 2 d) := by
  intro j i
  fin_cases j <;> simp [cc_pt, cc_zero]

theorem eval_first_axis_restrict (g : PS k 2 d) :
    ev (n := 2) ![pt k d 0] (ev (n := 1) ![pt k d 0, 0] g) = ev (n := 2) ![pt k d 0, 0] g := by
  rw [ev_ev zero_constant_first_point cz1]
  congr 1
  funext j i
  fin_cases j <;> simp [pt_apply, ev_X zero_constant_first_point, ev_zero' zero_constant_first_point]

end Gen

section Fam

variable {R : Type} [CommRing R] {k : Type} [CommRing k] [Algebra R k] {d : ℕ}

theorem integral_family_first_zero_second : ∀ j i, (![pt k (n := 2) d 0, 0, pt k d 1] : Fin 3 → Pt k 2 d) j i ∈ Ig R k (Fin 2 × Fin d) := by
  intro j i
  fin_cases j <;> simp [ig_pt, Subring.zero_mem]

theorem ig_fam_0z : ∀ j i, (![0, pt k (n := 2) d 1] : Fin 2 → Pt k 2 d) j i ∈ Ig R k (Fin 2 × Fin d) := by
  intro j i
  fin_cases j <;> simp [ig_pt, Subring.zero_mem]

end Fam

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k]

theorem constantCoeff_second_factor (B : FB R d O) : constantCoeff B.ph2 = 1 := by
  have h := congrArg constantCoeff B.cocycleRight_zero_fst
  rwa [cc_ev' (by intro j i; fin_cases j <;> simp [cc_pt, cc_zero]), map_one] at h

theorem cc_sy (B : FB R d O) : constantCoeff B.sy = 1 := by
  have h := congrArg constantCoeff B.symmetry_zero_fst
  rwa [cc_ev' (by intro j i; fin_cases j <;> simp [cc_pt, cc_zero]), map_one] at h

theorem cc_ad (B : FB R d O) (a : O) : constantCoeff (B.ad a) = 1 := by
  have h := congrArg constantCoeff (B.adjoint_zero_fst a)
  rwa [cc_ev' (by intro j i; fin_cases j <;> simp [cc_pt, cc_zero]), map_one] at h

theorem constantCoeff_add_second_third (B : FB R d O) (l : Fin d) :
    constantCoeff (addOf (B.FK k) (pt k (n := 3) d 1) (pt k d 2) l) = 0 := constantCoeff_ev cz12 ((lawK k B).const l)

theorem second_derivative_shift_integral {B : FB R d O} {h : PS k 2 d} (hc : B.IsCanonGauge k h) (b : Fin d) :
    ∑ c, pderiv k ((1 : Fin 2), c) h * ev (n := 2) ![pt k d 1] (Jac (lawK k B) c b) +
      ev (n := 2) ![pt k d 0] (sgOf k h b) ∈ Ig R k (Fin 2 × Fin d) := by
  set A : Pt k 3 d := addOf (B.FK k) (pt k (n := 3) d 1) (pt k d 2) with hA
  have c02 : CZ (![pt k (n := 3) d 0, pt k d 2] : Fin 2 → Pt k 3 d) :=
    CZ.cons (cc_pt 0) (CZ.cons (cc_pt 2) CZ.nil)
  have c0A : CZ (![pt k (n := 3) d 0, A] : Fin 2 → Pt k 3 d) :=
    CZ.cons (cc_pt 0) (CZ.cons (constantCoeff_add_second_third B) CZ.nil)
  have hh : constantCoeff h = 0 := by
    have := congrArg constantCoeff hc.ax1
    rwa [cc_ev' cz1, map_zero] at this

  set H := ev (n := 3) ![pt k d 0, pt k d 1] h + ev (n := 3) ![pt k d 0, pt k d 2] h -
    ev (n := 3) ![pt k d 0, A] h with hH
  have hcH : constantCoeff H = 0 := by
    rw [hH, map_sub, map_add, cc_ev' cz01, cc_ev' c02, cc_ev' c0A, hh]
    simp
  have hI : pderiv k ((2 : Fin 3), b) H ∈ Ig R k (Fin 3 × Fin d) :=
    ig_dlog B.ph2 (constantCoeff_second_factor B) H hcH hc.ph2 _
  have hG := ig_ev (R := R) czZ integral_family_pair_zero hI

  have dA : ∀ c, pderiv k ((2 : Fin 3), b) (A c) =
      ev (n := 3) ![pt k d 1, pt k d 2] (pderiv k ((1 : Fin 2), b) (B.FK k c)) := by
    intro c
    show pderiv k _ (ev (n := 3) ![pt k d 1, pt k d 2] (B.FK k c)) = _
    rw [d2 cz12]
    simp [pderiv_pt]
  have step1 : pderiv k ((2 : Fin 3), b) H =
      ev (n := 3) ![pt k d 0, pt k d 2] (pderiv k ((1 : Fin 2), b) h) -
        ∑ c, ev (n := 3) ![pt k d 0, A] (pderiv k ((1 : Fin 2), c) h) *
          ev (n := 3) ![pt k d 1, pt k d 2] (pderiv k ((1 : Fin 2), b) (B.FK k c)) := by
    rw [hH, map_sub, map_add, pderiv_ev_zero cz01 h _ ?_, d2 c02, d2 c0A]
    · simp only [dA]
      simp [pderiv_pt]
    · intro j i
      fin_cases j <;> simp [pderiv_pt]

  have e02 : (fun j i => ev (n := 2) ![pt k d 0, pt k d 1, 0]
      ((![pt k (n := 3) d 0, pt k d 2] : Fin 2 → Pt k 3 d) j i)) = ![pt k (n := 2) d 0, 0] := by
    funext j i
    fin_cases j <;> simp [pt_apply, ev_X czZ, ev_zero' czZ]
  have e12 : (fun j i => ev (n := 2) ![pt k d 0, pt k d 1, 0]
      ((![pt k (n := 3) d 1, pt k d 2] : Fin 2 → Pt k 3 d) j i)) = ![pt k (n := 2) d 1, 0] := by
    funext j i
    fin_cases j <;> simp [pt_apply, ev_X czZ, ev_zero' czZ]
  have e0A : (fun j i => ev (n := 2) ![pt k d 0, pt k d 1, 0]
      ((![pt k (n := 3) d 0, A] : Fin 2 → Pt k 3 d) j i)) = ![pt k (n := 2) d 0, pt k d 1] := by
    funext j i
    fin_cases j
    · simp [pt_apply, ev_X czZ]
    · show ev (n := 2) ![pt k d 0, pt k d 1, 0] (ev (n := 3) ![pt k d 1, pt k d 2] (B.FK k i)) = pt k d 1 i
      rw [ev_ev czZ cz12, e12, ← formal_ev_second_point_of_x_zero,
        show ev (n := 1) ![pt k d 0, 0] (B.FK k i) = (X ((0 : Fin 1), i) : PS k 1 d) from
          formalGroupLaw_ev_x_zero (G := lawK k B) i, ev_X czY]
      rfl
  have e01 : (![pt k (n := 2) d 0, pt k d 1] : Fin 2 → Pt k 2 d) = fun j => pt k d j := by
    funext j
    fin_cases j <;> rfl
  have key : ev (n := 2) ![pt k d 0, pt k d 1, 0] (pderiv k ((2 : Fin 3), b) H) =
      ev (n := 2) ![pt k d 0, 0] (pderiv k ((1 : Fin 2), b) h) -
        ∑ c, pderiv k ((1 : Fin 2), c) h * ev (n := 2) ![pt k d 1] (Jac (lawK k B) c b) := by
    rw [step1, ev_sub czZ, ev_ev czZ c02, e02, ev_sum czZ]
    congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [ev_mul czZ, ev_ev czZ c0A, e0A, e01, ev_pt, ev_ev czZ cz12, e12, ← formal_ev_second_point_of_x_zero]
    rfl
  have tgt : ∑ c, pderiv k ((1 : Fin 2), c) h * ev (n := 2) ![pt k d 1] (Jac (lawK k B) c b) +
      ev (n := 2) ![pt k d 0] (sgOf k h b) =
        -ev (n := 2) ![pt k d 0, pt k d 1, 0] (pderiv k ((2 : Fin 3), b) H) := by
    rw [key, sgOf, ev_neg zero_constant_first_point, eval_first_axis_restrict]
    ring
  rw [tgt]
  exact neg_mem hG

end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
