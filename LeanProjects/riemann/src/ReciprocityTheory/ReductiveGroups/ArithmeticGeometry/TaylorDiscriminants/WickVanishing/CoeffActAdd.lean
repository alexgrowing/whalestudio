import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.FirstDerivativeShiftIntegral

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB.LogPf

namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab

theorem coeff_single_zero_F_eq_ite {K : Type} [CommRing K] {d : ℕ} (G : FGLaw K d) (c i : Fin d) :
    coeff (Finsupp.single ((0 : Fin 2), i) 1) (G.F c) = if c = i then 1 else 0 := by
  classical
  have h := congrArg (coeff (Finsupp.single ((0 : Fin 1), i) 1)) (formalGroupLaw_ev_x_zero G c)
  rw [coeff_ev_zero_right, Finsupp.embDomain_single] at h
  rw [show (eXv d) ((0 : Fin 1), i) = ((0 : Fin 2), i) from rfl] at h
  rw [h, coeff_X]
  by_cases hci : c = i
  · subst hci; simp
  · rw [if_neg, if_neg hci]
    intro he
    exact hci (congrArg Prod.snd (Finsupp.single_left_injective one_ne_zero he)).symm

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]

theorem coeff_act_add (B : FB R d O) (a b : O) (i j : Fin d) :
    coeff (Finsupp.single ((0 : Fin 1), j) 1) (B.A.act (a + b) i) =
      coeff (Finsupp.single ((0 : Fin 1), j) 1) (B.A.act a i) + coeff (Finsupp.single ((0 : Fin 1), j) 1) (B.A.act b i) := by
  rw [B.A.add_act a b]
  show coeff _ (ev (n := 1) ![B.A.act a, B.A.act b] (B.G.F i)) = _
  have hab : CZ (![B.A.act a, B.A.act b] : Fin 2 → Pt R 1 d) := CZ.cons (B.A.const a) (CZ.cons (B.A.const b) CZ.nil)
  rw [← cc_pderiv', ← cc_pderiv' (B.A.act a i), ← cc_pderiv' (B.A.act b i), d2 hab]
  simp only [map_add, map_sum, map_mul, cc_ev' hab, cc_pderiv', coeff_single_zero_F_eq_ite, coeff_F_y, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]

variable {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k]

theorem dAct_sum (B : FB R d O) (w0 : O) (hw : w0 + star w0 = 1) (i j : Fin d) :
    dAct k B w0 i j + dAct k B (star w0) i j = if i = j then 1 else 0 := by
  simp only [dAct, FB.actK, MvPowerSeries.coeff_map]
  rw [← map_add, ← coeff_act_add, hw, B.A.one_act]
  simp only [pt, MvPowerSeries.coeff_X]
  by_cases h : i = j
  · subst h
    simp
  · have h' : Finsupp.single ((0 : Fin 1), j) 1 ≠ Finsupp.single ((0 : Fin 1), i) 1 := by
      intro e
      rw [Finsupp.single_left_inj one_ne_zero] at e
      exact h (Prod.mk.inj e).2.symm
    simp [h, h']

theorem homK (B : FB R d O) (a : O) (c : Fin d) :
    ev (n := 2) ![(lawK k B).F] (B.actK k a c) =
      ev (n := 2) ![comp1 (B.actK k a) (pt k (n := 2) d 0), comp1 (B.actK k a) (pt k (n := 2) d 1)] (B.FK k c) := by
  have h := congrArg (fun P : Pt R 2 d => MvPowerSeries.map (algebraMap R k) (P c)) (B.A.hom a)
  simp only [comp1, FGLaw.add, addOf] at h
  have c01 : CZ (![pt R (n := 2) d 0, pt R d 1] : Fin 2 → Pt R 2 d) := CZ.cons (cc_pt 0) (CZ.cons (cc_pt 1) CZ.nil)
  have cL : CZ (![addOf B.G.F (pt R (n := 2) d 0) (pt R d 1)] : Fin 1 → Pt R 2 d) :=
    CZ.cons (fun i => constantCoeff_ev c01 (B.G.const i)) CZ.nil
  have cR : CZ (![comp1 (B.A.act a) (pt R (n := 2) d 0), comp1 (B.A.act a) (pt R (n := 2) d 1)] : Fin 2 → Pt R 2 d) :=
    CZ.cons (fun i => constantCoeff_ev zero_constant_first_point (B.A.const a i)) (CZ.cons (fun i => constantCoeff_ev czY (B.A.const a i)) CZ.nil)
  rw [map_ev _ cL, map_ev _ cR] at h
  have m1 : ∀ i, MvPowerSeries.map (algebraMap R k) (addOf B.G.F (pt R (n := 2) d 0) (pt R d 1) i) = B.FK k i := by
    intro i
    show MvPowerSeries.map (algebraMap R k) (ev (n := 2) ![pt R d 0, pt R d 1] (B.G.F i)) = _
    rw [map_ev _ c01]
    have : (fun j c => MvPowerSeries.map (algebraMap R k) ((![pt R (n := 2) d 0, pt R d 1] : Fin 2 → Pt R 2 d) j c)) =
        fun j => pt k (n := 2) d j := by
      funext j c; fin_cases j <;> simp [pt_apply]
    rw [this, ev_pt]
    rfl
  have m2 : ∀ (l : Fin 2) (i : Fin d), MvPowerSeries.map (algebraMap R k) (comp1 (B.A.act a) (pt R (n := 2) d l) i) =
      comp1 (B.actK k a) (pt k (n := 2) d l) i := by
    intro l i
    show MvPowerSeries.map (algebraMap R k) (ev (n := 2) ![pt R d l] (B.A.act a i)) = ev (n := 2) ![pt k d l] (B.actK k a i)
    rw [map_ev _ (CZ.cons (cc_pt l) CZ.nil)]
    congr 1
    funext j c; fin_cases j; simp [pt_apply]
  have fL : (fun j i => MvPowerSeries.map (algebraMap R k)
      ((![addOf B.G.F (pt R (n := 2) d 0) (pt R d 1)] : Fin 1 → Pt R 2 d) j i)) = ![(lawK k B).F] := by
    funext j i; fin_cases j; exact m1 i
  have fR : (fun j i => MvPowerSeries.map (algebraMap R k)
      ((![comp1 (B.A.act a) (pt R (n := 2) d 0), comp1 (B.A.act a) (pt R (n := 2) d 1)] : Fin 2 → Pt R 2 d) j i)) =
      ![comp1 (B.actK k a) (pt k (n := 2) d 0), comp1 (B.actK k a) (pt k (n := 2) d 1)] := by
    funext j i; fin_cases j
    · exact m2 0 i
    · exact m2 1 i
  rw [fL, fR] at h
  exact h

theorem hom_rel (B : FB R d O) (a : O) (c b : Fin d) :
    ∑ j, pderiv k ((0 : Fin 1), j) (B.actK k a c) * Jac (lawK k B) j b =
      ∑ j, ev (n := 1) ![B.actK k a] (Jac (lawK k B) c j) * C (dAct k B a j b) := by
  have cP : CZ (![comp1 (B.actK k a) (pt k (n := 2) d 0), comp1 (B.actK k a) (pt k (n := 2) d 1)] : Fin 2 → Pt k 2 d) :=
    CZ.cons (fun l => constantCoeff_ev zero_constant_first_point (const_actK' B a l)) (CZ.cons (fun l => constantCoeff_ev czY (const_actK' B a l)) CZ.nil)
  have cAk : CZ (![B.actK k a] : Fin 1 → Pt k 1 d) := CZ.cons (const_actK' B a) CZ.nil
  have h := congrArg (fun g => ev (n := 1) ![pt k d 0, 0] (pderiv k ((1 : Fin 2), b) g)) (homK B a c)
  beta_reduce at h
  have z0 : ∀ j, pderiv k ((1 : Fin 2), b) (comp1 (B.actK k a) (pt k (n := 2) d 0) j) = 0 := fun j =>
    pderiv_ev_zero zero_constant_first_point _ _ (fun j l => by fin_cases j; simp [pderiv_pt])
  have zA : ∀ j, pderiv k ((1 : Fin 2), b) (comp1 (B.actK k a) (pt k (n := 2) d 1) j) =
      ev (n := 2) ![pt k d 1] (pderiv k ((0 : Fin 1), b) (B.actK k a j)) := fun j => d_y _ b
  have e1 : ∀ g : PS k 2 d, ev (n := 1) ![pt k d 0, 0]
      (ev (n := 2) ![comp1 (B.actK k a) (pt k (n := 2) d 0), comp1 (B.actK k a) (pt k (n := 2) d 1)] g) =
      ev (n := 1) ![B.actK k a] (ev (n := 1) ![pt k d 0, 0] g) := by
    intro g
    rw [ev_ev cz1 cP, ev_ev cAk cz1]
    congr 1
    funext j c
    fin_cases j
    · show ev (n := 1) ![pt k d 0, 0] (ev (n := 2) ![pt k d 0] (B.actK k a c)) = _
      rw [ev_ev cz1 zero_constant_first_point]
      have : (fun j c => ev (n := 1) ![pt k d 0, 0] ((![pt k (n := 2) d 0] : Fin 1 → Pt k 2 d) j c)) =
          (![pt k (n := 1) d 0] : Fin 1 → Pt k 1 d) := by
        funext j c; fin_cases j; simp [pt_apply, ev_X cz1]
      rw [this, gt_ev_pt_self]
      simp [pt_apply, ev_X cAk]
    · show ev (n := 1) ![pt k d 0, 0] (ev (n := 2) ![pt k d 1] (B.actK k a c)) = _
      rw [ez_y, const_actK', map_zero]
      simp [ev_zero' cAk]
  rw [d_F, d2 cP] at h
  simp only [z0, mul_zero, Finset.sum_const_zero, zero_add, zA, ev_sum cz1, ev_mul cz1, ezF, ez_dF, e1, ez_y,
    cc_pderiv'] at h
  rw [h]
  rfl

end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
