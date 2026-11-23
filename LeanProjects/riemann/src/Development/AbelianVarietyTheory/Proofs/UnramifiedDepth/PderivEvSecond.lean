import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ChartChg
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.IntegralFamilyFirstZeroSecond

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.LogPf
  ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab

namespace GlobalTheory.GaugeSecondDeriv

variable {k : Type} [CommRing k] {d : ℕ}

theorem cz12 : CZ (![pt k (n := 3) d 1, pt k d 2] : Fin 2 → Pt k 3 d) :=
  CZ.cons (cc_pt 1) (CZ.cons (cc_pt 2) CZ.nil)

theorem pderiv_ev_second (h : PS k 2 d) (q : Pt k 3 d) (hq : ∀ c, constantCoeff (q c) = 0) (b : Fin d) :
    pderiv k ((2 : Fin 3), b) (ev (n := 3) ![pt k d 0, q] h) =
      ∑ j, ev (n := 3) ![pt k d 0, q] (pderiv k ((1 : Fin 2), j) h) * pderiv k ((2 : Fin 3), b) (q j) := by
  have hc : CZ (![pt k (n := 3) d 0, q] : Fin 2 → Pt k 3 d) := CZ.cons (cc_pt 0) (CZ.cons hq CZ.nil)
  rw [pderiv_ev hc, Fintype.sum_prod_type, Fin.sum_univ_two]
  simp [pderiv_pt]

theorem ev_pderiv_add (F : PS k 2 d) (b : Fin d) :
    ev (n := 2) ![pt k d 0, pt k d 1, 0]
      (pderiv k ((2 : Fin 3), b) (ev (n := 3) ![pt k d 1, pt k d 2] F)) =
      ev (n := 2) ![pt k d 1, 0] (pderiv k ((1 : Fin 2), b) F) := by
  rw [pderiv_ev cz12, Fintype.sum_prod_type, Fin.sum_univ_two]
  have e : ((1 : Fin 3) = 2) = False := by simp
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, pderiv_pt, Prod.mk.injEq, e, false_and,
    if_false, mul_zero, Finset.sum_const_zero, zero_add, true_and, mul_ite, mul_one,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [ev_ev czZ cz12]
  congr 1
  funext j c
  fin_cases j <;> simp [pt_apply, ev_X czZ]

theorem ev_add_axis (G : FGLaw k d) (c : Fin d) :
    ev (n := 2) ![pt k d 0, pt k d 1, 0] (ev (n := 3) ![pt k d 1, pt k d 2] (G.F c)) =
      pt k (n := 2) d 1 c := by
  have h1 : CZ (![pt k (n := 2) d 1] : Fin 1 → Pt k 2 d) := CZ.cons (cc_pt 1) CZ.nil
  have e := congrArg (ev (n := 2) ![pt k d 1]) (formalGroupLaw_ev_x_zero G c)
  rw [ev_ev h1 cz1, ev_X h1] at e
  rw [ev_ev czZ cz12]
  refine Eq.trans ?_ e
  congr 1
  funext j c
  fin_cases j <;> simp [pt_apply, ev_X czZ, ev_X h1, ev_zero' h1]

theorem main : (∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h : PS k 2 d), B.IsCanonGauge k h → ∀ b : Fin d, ∃ K : PS R 2 d, ∑ j, ev (n := 2) ![pt k d 1, 0] (pderiv k ((1 : Fin 2), b) (B.FK k j)) * pderiv k ((1 : Fin 2), j) h =
    FB.toK k K + ev (n := 2) ![pt k d 0, 0] (pderiv k ((1 : Fin 2), b) h)) := by
  intro R _ d O _ _ k _ _ _ B h hc b
  have hA : ∀ c, constantCoeff (addOf (B.FK k) (pt k (n := 3) d 1) (pt k d 2) c) = 0 :=
    fun c => constantCoeff_ev cz12 ((lawK k B).const c)
  have c02 : CZ (![pt k (n := 3) d 0, pt k d 2] : Fin 2 → Pt k 3 d) :=
    CZ.cons (cc_pt 0) (CZ.cons (cc_pt 2) CZ.nil)
  have cA : CZ (![pt k (n := 3) d 0, addOf (B.FK k) (pt k (n := 3) d 1) (pt k d 2)] : Fin 2 → Pt k 3 d) :=
    CZ.cons (cc_pt 0) (CZ.cons hA CZ.nil)
  have hH0 : constantCoeff (ev (n := 3) ![pt k d 0, pt k d 1] h + ev (n := 3) ![pt k d 0, pt k d 2] h -
      ev (n := 3) ![pt k d 0, addOf (B.FK k) (pt k d 1) (pt k d 2)] h) = 0 := by
    rw [map_sub, map_add, cc_ev' cz01, cc_ev' c02, cc_ev' cA, cc_h hc]
    simp
  have hH := ig_dlog B.ph2 (constantCoeff_second_factor B) _ hH0 hc.ph2 ((2 : Fin 3), b)
  have h2 := ig_ev czZ integral_family_pair_zero hH
  have t1 : pderiv k ((2 : Fin 3), b) (ev (n := 3) ![pt k d 0, pt k d 1] h) = 0 :=
    pderiv_ev_zero cz01 _ _ (fun j l => by fin_cases j <;> simp [pderiv_pt])
  have t2 : ev (n := 2) ![pt k d 0, pt k d 1, 0]
      (pderiv k ((2 : Fin 3), b) (ev (n := 3) ![pt k d 0, pt k d 2] h)) =
      ev (n := 2) ![pt k d 0, 0] (pderiv k ((1 : Fin 2), b) h) := by
    rw [pderiv_ev_second h _ (cc_pt 2)]
    simp only [pderiv_pt, Prod.mk.injEq, true_and, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [ev_ev czZ c02]
    congr 1
    funext j c
    fin_cases j <;> simp [pt_apply, ev_X czZ]
  have t3 : ev (n := 2) ![pt k d 0, pt k d 1, 0] (pderiv k ((2 : Fin 3), b)
      (ev (n := 3) ![pt k d 0, addOf (B.FK k) (pt k d 1) (pt k d 2)] h)) =
      ∑ j, ev (n := 2) ![pt k d 1, 0] (pderiv k ((1 : Fin 2), b) (B.FK k j)) *
        pderiv k ((1 : Fin 2), j) h := by
    rw [pderiv_ev_second h _ hA, ev_sum czZ]
    refine Finset.sum_congr rfl fun j _ => ?_
    have e : (fun i c => ev (n := 2) ![pt k d 0, pt k d 1, 0]
        ((![pt k (n := 3) d 0, addOf (B.FK k) (pt k (n := 3) d 1) (pt k d 2)] : Fin 2 → Pt k 3 d) i c)) =
        fun i => pt k (n := 2) d i := by
      funext i c
      fin_cases i
      · simp [pt_apply, ev_X czZ]
      · exact ev_add_axis (lawK k B) c
    rw [ev_mul czZ, ev_ev czZ cA, e, ev_pt, mul_comm]
    congr 1
    exact ev_pderiv_add (B.FK k j) b
  rw [map_sub, map_add, t1, zero_add, ev_sub czZ, t2, t3] at h2
  obtain ⟨K, hK⟩ := RingHom.mem_range.1 h2
  refine ⟨-K, ?_⟩
  rw [FB.toK, map_neg, hK]
  ring

end GlobalTheory.GaugeSecondDeriv
