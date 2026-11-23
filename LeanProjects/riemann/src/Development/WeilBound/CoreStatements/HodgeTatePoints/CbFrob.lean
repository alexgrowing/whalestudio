import Development.WeilBound.CoreStatements.HodgeTatePoints.FirstPowerEqProdAt
import Development.WeilBound.CoreStatements.HodgeTatePoints.CoeffEvPowOne

noncomputable section

namespace PositivityTheory.HtPt.Cb

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open ReciprocityTheory.ChartRestriction.G.TB

section

variable {R : Type} [CommRing R] {d m n : ℕ}

theorem ev_at_zero (f : PS R 1 d) : ev ![(0 : Pt R n d)] f = C (constantCoeff f) := by
  ext e
  have ha : HasSubst (fun q : Fin 1 × Fin d => (![(0 : Pt R n d)] q.1 q.2)) :=
    hasSubst_ev _ (by intro j i; simp)
  rw [ev, coeff_subst ha, finsum_eq_single _ 0]
  · simp [coeff_C, coeff_one]
  · intro d' hd'
    obtain ⟨s, hs⟩ : ∃ s, d' s ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hd' (Finsupp.ext hcon)
    have hz : (![(0 : Pt R n d)] s.1 s.2) ^ d' s = 0 := by simp [zero_pow hs]
    rw [Finsupp.prod, Finset.prod_eq_zero (Finsupp.mem_support_iff.2 hs) hz]
    simp

theorem dcomp_ne {s t : Fin n} (h : t ≠ s) (φ : Pt R 1 d) (j c : Fin d) :
    pderiv R (s, j) (comp1 φ (pt R d t) c) = 0 := by
  show pderiv R (s, j) (ev ![pt R d t] (φ c)) = 0
  rw [d1 (Z_pt t)]
  simp [dpt, h]

theorem dcomp_eq (s : Fin n) (φ : Pt R 1 d) (j c : Fin d) :
    pderiv R (s, j) (comp1 φ (pt R d s) c) = ev ![pt R d s] (pderiv R ((0 : Fin 1), j) (φ c)) := by
  show pderiv R (s, j) (ev ![pt R d s] (φ c)) = _
  rw [d1 (Z_pt s)]
  simp [dpt]

theorem jac_cancel (G : FGLaw R d) {x : Pt R n d} (hx : Z x) (v : Fin d → PS R n d)
    (h : ∀ j, ∑ c, v c * ev ![x, 0] (pderiv R ((1 : Fin 2), j) (G.F c)) = 0) (c : Fin d) : v c = 0 := by
  let M : Matrix (Fin d) (Fin d) (PS R n d) := fun c j => ev ![x, 0] (pderiv R ((1 : Fin 2), j) (G.F c))
  have hb : ZZ ![x, (0 : Pt R n d)] := ZZ_cons hx (ZZ_cons Z_zero ZZ_nil)
  have hb0 : ZZ (n := 1) ![(0 : Pt R 1 d), pt R d 0] := ZZ_cons Z_zero (ZZ_cons (Z_pt 0) ZZ_nil)
  have hcc : ∀ c j, constantCoeff (M c j) = if c = j then 1 else 0 := by
    intro c j
    show constantCoeff (ev ![x, 0] (pderiv R ((1 : Fin 2), j) (G.F c))) = _
    rw [ccev hb, cc_pderiv]
    have hu : constantCoeff (pderiv R ((0 : Fin 1), j) (ev ![(0 : Pt R 1 d), pt R d 0] (G.F c))) =
        constantCoeff (pderiv R ((0 : Fin 1), j) (pt R d 0 c)) := by
      rw [G.unit c]
      rfl
    rw [d2 Z_zero (Z_pt 0), dpt] at hu
    simp [dpt, ccev hb0, cc_pderiv] at hu
    rw [hu]
  have hdet : IsUnit M.det := by
    rw [MvPowerSeries.isUnit_iff_constantCoeff, RingHom.map_det]
    have h1 : (constantCoeff : PS R n d →+* R).mapMatrix M = 1 := by
      ext c j
      simp [hcc, Matrix.one_apply]
    rw [h1, Matrix.det_one]
    exact isUnit_one
  have hv : Matrix.vecMul v M = 0 := by
    funext j
    exact h j
  have hv' : v = Matrix.vecMul (Matrix.vecMul v M) M⁻¹ := by
    rw [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hdet, Matrix.vecMul_one]
  rw [hv', hv, Matrix.zero_vecMul]
  rfl

theorem ev_d_prod {b : Fin m → Pt R n d} (hb : ZZ b) (v : Fin m × Fin d) (f : ℕ → PS R m d)
    (h : ∀ k, ev b (pderiv R v (f k)) = 0) (N : ℕ) : ev b (pderiv R v (∏ k ∈ Finset.range N, f k)) = 0 := by
  induction N with
  | zero => simp [evz hb]
  | succ N ih =>
    rw [Finset.prod_range_succ, dmul, eva hb, evm hb, evm hb, ih, h, zero_mul, mul_zero, add_zero]

theorem d_pow_p (p : ℕ) [CharP R p] (v : Fin n × Fin d) (f : PS R n d) : pderiv R v (f ^ p) = 0 := by
  rw [Derivation.leibniz_pow]
  have hp : (p : R) = 0 := CharP.cast_eq_zero R p
  have h0 : (p : MvPowerSeries (Fin n × Fin d) R) = 0 := by
    rw [← map_natCast (algebraMap R (MvPowerSeries (Fin n × Fin d) R)), hp, map_zero]
  rw [nsmul_eq_mul, h0, zero_mul]

variable {O : Type} [CommRing O]

theorem d_act_p (p : ℕ) [CharP R p] {G : FGLaw R d} (A : OAct O G) (i j : Fin d) :
    pderiv R ((0 : Fin 1), j) (A.act (p : O) i) = 0 := by
  have hb : ZZ (n := 1) ![pt R d 0, (0 : Pt R 1 d)] := ZZ_cons (Z_pt 0) (ZZ_cons Z_zero ZZ_nil)
  have hp0 : ∀ e k : Fin d, coeff (Finsupp.single ((0 : Fin 1), k) 1) (A.act (p : O) e) = 0 := by
    intro e k
    have h1 := congrFun (congrFun (lin_act_nat A p) e) k
    simp only [lin] at h1
    rw [h1]
    simp [Matrix.one_apply, CharP.cast_eq_zero]
  refine jac_cancel G (Z_pt (R := R) (d := d) (n := 1) 0)
    (fun c => pderiv R ((0 : Fin 1), c) (A.act (p : O) i)) (fun k => ?_) j
  have L : ev ![pt R d 0, (0 : Pt R 1 d)]
      (pderiv R ((1 : Fin 2), k) (comp1 (A.act (p : O)) (G.add (pt R d 0) (pt R d 1)) i)) =
      ∑ c, pderiv R ((0 : Fin 1), c) (A.act (p : O) i) *
        ev ![pt R d 0, (0 : Pt R 1 d)] (pderiv R ((1 : Fin 2), k) (G.F c)) := by
    show ev _ (pderiv R _ (ev ![G.add (pt R d 0) (pt R d 1)] (A.act (p : O) i))) = _
    rw [d1 (Z_add G (Z_pt 0) (Z_pt 1)), evsum hb]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [evm hb, ev1 hb (Z_add G (Z_pt 0) (Z_pt 1)), ep_add G hb (Z_pt 0) (Z_pt 1), ep_pt hb, ep_pt hb]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, p_add_zero G (Z_pt 0)]
    congr 1
    · exact ev_pt_self _ (fun l => by fin_cases l; rfl) _
    · show ev _ (pderiv R _ (ev ![pt R d 0, pt R d 1] (G.F c))) = _
      rw [eval_points_two]
  have Rt : ev ![pt R d 0, (0 : Pt R 1 d)]
      (pderiv R ((1 : Fin 2), k) (G.add (comp1 (A.act (p : O)) (pt R d 0))
        (comp1 (A.act (p : O)) (pt R d 1)) i)) = 0 := by
    show ev _ (pderiv R _ (ev ![comp1 (A.act (p : O)) (pt R d 0), comp1 (A.act (p : O)) (pt R d 1)]
      (G.F i))) = 0
    rw [d2 (Z_comp1 (Z_act A _) (Z_pt 0)) (Z_comp1 (Z_act A _) (Z_pt 1))]
    simp only [dcomp_ne (show (0 : Fin 2) ≠ 1 by decide), dcomp_eq, mul_zero, Finset.sum_const_zero,
      zero_add, evsum hb, evm hb]
    refine Finset.sum_eq_zero fun e _ => ?_
    rw [ev1 hb (Z_pt 1), ep_pt hb]
    simp only [Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero, ev_at_zero, cc_pderiv,
      hp0, map_zero, mul_zero]
  have e := congrArg (fun F : Pt R 2 d => ev ![pt R d 0, (0 : Pt R 1 d)]
    (pderiv R ((1 : Fin 2), k) (F i))) (A.hom (p : O))
  rw [L, Rt] at e
  exact e

variable [StarRing O] (B : FB R d O)

theorem deriv_first_first_form_zero {z : Pt R n d} (hz : Z z) (c : Fin d) : ev ![0, 0, z] (pderiv R ((0 : Fin 3), c) B.ph1) = 0 := by
  have hb : ZZ ![(0 : Pt R n d), z] := ZZ_cons Z_zero (ZZ_cons hz ZZ_nil)
  have e0 : pderiv R ((0 : Fin 2), c) (ev ![pt R d 0, 0, pt R d 1] B.ph1) = 0 := by
    rw [B.cocycleLeft_zero_snd]
    exact Derivation.map_one_eq_zero _
  rw [d3 (Z_pt 0) Z_zero (Z_pt 1)] at e0
  simp [dpt] at e0
  have e1 := congrArg (ev ![(0 : Pt R n d), z]) e0
  rw [ev3 hb (Z_pt 0) Z_zero (Z_pt 1), ep_pt hb, ep_zero hb, ep_pt hb, evz hb] at e1
  simpa using e1

theorem deriv_second_first_form_zero {z : Pt R n d} (hz : Z z) (c : Fin d) : ev ![0, 0, z] (pderiv R ((1 : Fin 3), c) B.ph1) = 0 := by
  have hb : ZZ ![(0 : Pt R n d), z] := ZZ_cons Z_zero (ZZ_cons hz ZZ_nil)
  have e0 : pderiv R ((0 : Fin 2), c) (ev ![0, pt R d 0, pt R d 1] B.ph1) = 0 := by
    rw [B.cocycleLeft_zero_fst]
    exact Derivation.map_one_eq_zero _
  rw [d3 Z_zero (Z_pt 0) (Z_pt 1)] at e0
  simp [dpt] at e0
  have e1 := congrArg (ev ![(0 : Pt R n d), z]) e0
  rw [ev3 hb Z_zero (Z_pt 0) (Z_pt 1), ep_zero hb, ep_pt hb, ep_pt hb, evz hb] at e1
  simpa using e1

private theorem ev_zero_pderiv_pow1_eq_zero {z : Pt R n d} (hz : Z z) (k : Fin d) (N : ℕ) :
    ev ![(0 : Pt R n d), z] (pderiv R ((0 : Fin 2), k) (pow1 B N)) = 0 := by
  have hb : ZZ ![(0 : Pt R n d), z] := ZZ_cons Z_zero (ZZ_cons hz ZZ_nil)
  unfold pow1
  refine ev_d_prod hb _ _ (fun l => ?_) N
  rw [d3 (Z_comp1 (Z_act B.A _) (Z_pt 0)) (Z_pt 0) (Z_pt 1)]
  simp only [eva hb, evsum hb, evm hb, ev3 hb (Z_comp1 (Z_act B.A _) (Z_pt 0)) (Z_pt 0) (Z_pt 1),
    ep_comp1 _ hb (Z_pt 0), ep_pt hb, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    germComp1_zero_of_noConstantCoeff (Z_act _ _), deriv_first_first_form_zero B hz, deriv_second_first_form_zero B hz, zero_mul, Finset.sum_const_zero,
    zero_add]
  refine Finset.sum_eq_zero fun e _ => ?_
  simp [dpt, evz hb]

theorem deriv_first_power_char_p (p : ℕ) [CharP R p] (j : Fin d) : pderiv R ((0 : Fin 2), j) (pow1 B p) = 0 := by
  have hb : ZZ (n := 2) ![pt R d 0, 0, pt R d 1] :=
    ZZ_cons (Z_pt 0) (ZZ_cons Z_zero (ZZ_cons (Z_pt 1) ZZ_nil))
  refine jac_cancel B.G (Z_pt (R := R) (d := d) (n := 2) 0)
    (fun c => pderiv R ((0 : Fin 2), c) (pow1 B p)) (fun k => ?_) j
  have hadd : ∀ c, pderiv R ((1 : Fin 3), k) (B.G.add (pt R d 0) (pt R d 1) c) =
      ev ![pt R d 0, pt R d 1] (pderiv R ((1 : Fin 2), k) (B.G.F c)) := by
    intro c
    show pderiv R _ (ev ![pt R d 0, pt R d 1] (B.G.F c)) = _
    rw [d2 (Z_pt 0) (Z_pt 1)]
    simp [dpt]
  have hz2 : ∀ c, pderiv R ((1 : Fin 3), k) (pt R d 2 c) = 0 := by
    intro c
    simp [dpt]
  have L : ev ![pt R d 0, (0 : Pt R 2 d), pt R d 1] (pderiv R ((1 : Fin 3), k)
      (ev ![B.G.add (pt R d 0) (pt R d 1), pt R d 2] (pow1 B p) * B.ph1 ^ p)) =
      ∑ c, pderiv R ((0 : Fin 2), c) (pow1 B p) *
        ev ![pt R d 0, (0 : Pt R 2 d)] (pderiv R ((1 : Fin 2), k) (B.G.F c)) := by
    rw [dmul, d_pow_p, mul_zero, add_zero, evm hb, evpow hb, B.cocycleLeft_zero_snd, one_pow, mul_one,
      d2 (Z_add B.G (Z_pt 0) (Z_pt 1)) (Z_pt 2)]
    simp only [hz2, mul_zero, Finset.sum_const_zero, add_zero, evsum hb, evm hb, hadd,
      ev2 hb (Z_add B.G (Z_pt 0) (Z_pt 1)) (Z_pt 2), ev2 hb (Z_pt 0) (Z_pt 1),
      ep_add B.G hb (Z_pt 0) (Z_pt 1), ep_pt hb, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, p_add_zero B.G (Z_pt 0), eval_points_two]
  have hA : pderiv R ((1 : Fin 3), k) (ev ![pt R d 0, pt R d 2] (pow1 B p)) = 0 := by
    rw [d2 (Z_pt 0) (Z_pt 2)]
    simp [dpt]
  have hBq : ev ![pt R d 0, (0 : Pt R 2 d), pt R d 1]
      (pderiv R ((1 : Fin 3), k) (ev ![pt R d 1, pt R d 2] (pow1 B p))) = 0 := by
    rw [d2 (Z_pt 1) (Z_pt 2)]
    simp only [dpt, Prod.mk.injEq, true_and, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    simp [dpt]
    rw [ev2 hb (Z_pt 1) (Z_pt 2), ep_pt hb, ep_pt hb]
    simpa using ev_zero_pderiv_pow1_eq_zero B (Z_pt (R := R) (d := d) (n := 2) 1) k p
  have hC : pderiv R ((1 : Fin 3), k) (ev ![comp1 (B.A.act (p : O)) (pt R d 0),
      comp1 (B.A.act (p : O)) (pt R d 1), pt R d 2] B.ph1) = 0 := by
    rw [d3 (Z_comp1 (Z_act B.A _) (Z_pt 0)) (Z_comp1 (Z_act B.A _) (Z_pt 1)) (Z_pt 2)]
    have hq : ZZ (n := 3) ![pt R d 1] := ZZ_cons (Z_pt 1) ZZ_nil
    simp [dcomp_ne (show (0 : Fin 3) ≠ 1 by decide), dcomp_eq, d_act_p, evz hq, hz2]
  have e := congrArg (fun f : PS R 3 d => ev ![pt R d 0, (0 : Pt R 2 d), pt R d 1]
    (pderiv R ((1 : Fin 3), k) f)) (first_power_add R d O B p)
  rw [L, dmul, dmul, hA, hC, zero_mul, zero_add, mul_zero, add_zero, evm hb, evm hb, hBq,
    mul_zero, zero_mul] at e
  exact e

end

theorem mulp_V : ∀ (R : Type) [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O), ∃ V : Pt R 1 d, (∀ i, constantCoeff (V i) = 0) ∧ B.A.act (p : O) = comp1 V (ptPow R d p 0) ∧ lin V 1 = hw B p := by
  intro R _ p _ _ d O _ _ B
  have key : ∀ c, ∃ g : PS R 1 d, B.A.act (p : O) c = ev ![ptPow R d p 0] g := fun c =>
    (series_in_p R p d).1 _ (fun j => d_act_p p B.A c j)
  choose V hV using key
  have hq : ZZ (n := 1) ![ptPow R d p 0] := ZZ_cons (Z_ptPow p 0) ZZ_nil
  refine ⟨V, ?_, ?_, ?_⟩
  · intro c
    rw [← ccev hq (V c), ← hV c]
    exact B.A.const _ c
  · funext c
    exact hV c
  · ext c i
    show coeff _ (V c) = coeff _ (B.A.act (p : O) c)
    rw [hV c, coeff_ev_pow_one]

theorem first_power_char_p : ∀ (R : Type) [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O), ∃ g : PS R 2 d, AxOne g ∧ pow1 B p = ev (n := 2) ![ptPow R d p 0, pt R d 1] g ∧ bil g 1 1 = am B p := by
  intro R _ p _ _ d O _ _ B
  obtain ⟨g, hg⟩ := (series_in_p R p d).2 (pow1 B p) (fun j => deriv_first_power_char_p B p j)
  have hq : ZZ (n := 1) ![ptPow R d p 0] := ZZ_cons (Z_ptPow p 0) ZZ_nil
  refine ⟨g, And.intro ?_ ?_, hg, ?_⟩
  · have hb : ZZ (n := 1) ![(0 : Pt R 1 d), pt R d 0] := ZZ_cons Z_zero (ZZ_cons (Z_pt 0) ZZ_nil)
    have e := congrArg (ev ![(0 : Pt R 1 d), pt R d 0]) hg
    rw [first_power_zero_left B (Z_pt 0), ev2 hb (Z_ptPow p 0) (Z_pt 1), ep_ptPow p hb, ep_pt hb] at e
    refine Eq.trans ?_ e.symm
    congr 1
    funext k i
    fin_cases k
    · simp [(Fact.out : p.Prime).ne_zero]
    · rfl
  · have hb : ZZ (n := 1) ![pt R d 0, (0 : Pt R 1 d)] := ZZ_cons (Z_pt 0) (ZZ_cons Z_zero ZZ_nil)
    have e := congrArg (ev ![pt R d 0, (0 : Pt R 1 d)]) hg
    rw [first_power_zero_right B (Z_pt 0), ev2 hb (Z_ptPow p 0) (Z_pt 1), ep_ptPow p hb, ep_pt hb] at e
    apply ev_pow_inj p
    rw [ev2 hq (Z_pt 0) Z_zero, ep_pt hq, ep_zero hq, ev_one, e]
    congr 1
  · rw [← bil_ev_pow_two p g, ← hg]
    rfl

end PositivityTheory.HtPt.Cb
