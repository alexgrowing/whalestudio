import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GaugeTrans
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.CalcExp
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FormalSecondPointDerivativeSecondCoordinate
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PowerSeriesExpIntegralCanonGaugeAdditiveSecond

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB.WickVanishing GlobalTheory.QuadDeriv

namespace GlobalTheory.MatrixGauge

section Small

variable (R : Type) [CommRing R] {d : ℕ} {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k] {m : ℕ}

def Small (f : PS k m d) : Prop :=
  constantCoeff f = 0 ∧ ∃ w : PS R m d, constantCoeff w = 1 ∧ FB.toK k w = FB.expS k f

def IsBase (P : Pt k m d) : Prop := ∃ Q : Pt R m d, GP Q ∧ P = mapP (algebraMap R k) Q

variable {R}

theorem small_zero : Small R (0 : PS k m d) :=
  ⟨map_zero _, 1, map_one _, by
    rw [FB.toK, map_one, FB.expS, ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.exp_zero]⟩

theorem Small.congr {f g : PS k m d} (hf : Small R f) (e : f = g) : Small R g := e ▸ hf

theorem Small.add {f g : PS k m d} (hf : Small R f) (hg : Small R g) : Small R (f + g) := by
  obtain ⟨f0, v, v1, hv⟩ := hf
  obtain ⟨g0, w, w1, hw⟩ := hg
  refine ⟨by simp [f0, g0], v * w, by simp [v1, w1], ?_⟩
  rw [FB.toK, map_mul, gt_expS_add _ _ f0 g0]
  exact congrArg₂ (· * ·) hv hw

theorem Small.neg {f : PS k m d} (hf : Small R f) : Small R (-f) := by
  obtain ⟨f0, v, v1, hv⟩ := hf
  have n0 : constantCoeff (-f) = 0 := by simp [f0]
  refine ⟨n0, invOfUnit v 1, by simp, ?_⟩
  have h1 : FB.toK k v * FB.toK k (invOfUnit v 1) = 1 := by
    rw [FB.toK, FB.toK, ← map_mul, mul_invOfUnit v 1 (by simpa using v1), map_one]
  have h2 : FB.expS k (-f) * FB.expS k f = 1 := by
    rw [← gt_expS_add _ _ n0 f0, neg_add_cancel, FB.expS, ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.exp_zero]
  rw [hv] at h1
  calc FB.toK k (invOfUnit v 1) = (FB.expS k (-f) * FB.expS k f) * FB.toK k (invOfUnit v 1) := by
        rw [h2, _root_.one_mul]
    _ = FB.expS k (-f) := by rw [_root_.mul_assoc, h1, _root_.mul_one]

theorem Small.sum {ι : Type} (s : Finset ι) {f : ι → PS k m d} (hf : ∀ i, Small R (f i)) :
    Small R (∑ i ∈ s, f i) :=
  Finset.sum_induction f (Small R) (fun _ _ => Small.add) small_zero fun i _ => hf i

theorem Small.sum_sub {ι : Type} (s : Finset ι) {f g : ι → PS k m d} (hf : ∀ i, Small R (f i - g i)) :
    Small R (∑ i ∈ s, f i - ∑ i ∈ s, g i) :=
  (Small.sum s hf).congr (Finset.sum_sub_distrib _ _)

theorem Small.trans {f g e : PS k m d} (h1 : Small R (f - g)) (h2 : Small R (g - e)) : Small R (f - e) :=
  (h1.add h2).congr (by ring)

omit [Algebra ℚ k] in
theorem IsBase.gp {P : Pt k m d} (hP : IsBase R P) : GP P := by
  obtain ⟨Q, hQ, rfl⟩ := hP
  exact constantCoeff_mapP_eq_zero _ _ hQ

omit [Algebra ℚ k] in
theorem isBase_pt (j : Fin m) : IsBase R (pt k d j) := ⟨pt R d j, gp_pt j, (baseChange_pt _ j).symm⟩

omit [Algebra ℚ k] in
theorem isBase_zero : IsBase R (0 : Pt k m d) := ⟨0, gp_zero₂, funext fun _ => (map_zero _).symm⟩

theorem Small.subst {l : ℕ} {V : Fin l → Pt k m d} (hV : ∀ j, IsBase R (V j)) {f : PS k l d}
    (hf : Small R f) : Small R (ev V f) := by
  obtain ⟨f0, w, w1, hw⟩ := hf
  have hV' : ∀ j, GP (V j) := fun j => (hV j).gp
  choose a ha e using hV
  refine ⟨gt_const_ev V hV' f f0, ev a w, by rw [gt_const_ev_eq a ha, w1], ?_⟩
  rw [← gt_ev_expS V hV' f f0, ← hw, FB.toK, QuadDeriv.map_ev _ _ ha]
  congr 1
  funext j
  exact (e j).symm

omit [Algebra ℚ k] in
theorem isBase2 {P Q : Pt k m d} (hP : IsBase R P) (hQ : IsBase R Q) : ∀ j, IsBase R (![P, Q] j) := by
  intro j; fin_cases j
  · exact hP
  · exact hQ

omit [Algebra ℚ k] in
theorem isBase3 {P Q T : Pt k m d} (hP : IsBase R P) (hQ : IsBase R Q) (hT : IsBase R T) :
    ∀ j, IsBase R (![P, Q, T] j) := by
  intro j; fin_cases j
  · exact hP
  · exact hQ
  · exact hT

end Small

section Points

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
  {k : Type} [CommRing k] [Algebra R k] (B : FB R d O) {m : ℕ}

theorem gp_act (a : O) : GP (B.actK k a) := constantCoeff_mapP_eq_zero _ _ (B.A.const a)

theorem gp_law : GP (B.FK k) := constantCoeff_mapP_eq_zero _ _ B.G.const

theorem IsBase.act (a : O) {P : Pt k m d} (hP : IsBase R P) : IsBase R (comp1 (B.actK k a) P) := by
  obtain ⟨Q, hQ, rfl⟩ := hP
  exact ⟨comp1 (B.A.act a) Q, gp_comp1 _ _ (B.A.const a) hQ, (baseChange_comp1 _ _ _ hQ).symm⟩

theorem IsBase.add {P P' : Pt k m d} (hP : IsBase R P) (hP' : IsBase R P') :
    IsBase R (addOf (B.FK k) P P') := by
  obtain ⟨Q, hQ, rfl⟩ := hP
  obtain ⟨Q', hQ', rfl⟩ := hP'
  exact ⟨addOf B.G.F Q Q', gp_addOf _ B.G.const _ _ hQ hQ', (baseChange_addOf _ _ _ _ hQ hQ').symm⟩

theorem isBase_foldr {ι : Type} {g : ι → Pt k m d} (hg : ∀ b, IsBase R (g b)) (L : List ι) :
    IsBase R (L.foldr (fun b acc => addOf (B.FK k) (g b) acc) 0) := by
  induction L with
  | nil => exact isBase_zero
  | cons b L ih => exact (hg b).add B ih

theorem act_act (a c : O) {P : Pt k m d} (hP : GP P) :
    comp1 (B.actK k a) (comp1 (B.actK k c) P) = comp1 (B.actK k (a * c)) P := by
  rw [FramePull.actK_mul, gt_comp1_comp1 _ _ (gp_act B c) _ hP]

theorem add_act (a c : O) {P : Pt k m d} (hP : GP P) :
    comp1 (B.actK k (a + c)) P = addOf (B.FK k) (comp1 (B.actK k a) P) (comp1 (B.actK k c) P) := by
  rw [FramePull.actK_add]
  exact evP_addOf ![P] (single_point_zero_constant hP) _ _ _ (gp_act B a) (gp_act B c)

theorem act_add (a : O) {P Q : Pt k m d} (hP : IsBase R P) (hQ : IsBase R Q) :
    comp1 (B.actK k a) (addOf (B.FK k) P Q) =
      addOf (B.FK k) (comp1 (B.actK k a) P) (comp1 (B.actK k a) Q) := by
  obtain ⟨P, hP, rfl⟩ := hP
  obtain ⟨Q, hQ, rfl⟩ := hQ
  have hV := pair_points_zero_constant hP hQ
  have p0 : GP (pt R (n := 2) d 0) := gp_pt 0
  have p1 : GP (pt R (n := 2) d 1) := gp_pt 1
  have hc : ∀ {n : ℕ} {X : Pt R n d}, GP X → GP (comp1 (B.A.act a) X) :=
    fun hX => gp_comp1 _ _ (B.A.const a) hX
  have h1 := congrArg (evP ![P, Q]) (B.A.hom a)
  rw [evP_comp1 _ hV _ _ (gp_addOf _ B.G.const _ _ p0 p1), evP_addOf _ hV _ _ _ p0 p1,
    evP_addOf _ hV _ _ _ (hc p0) (hc p1), evP_comp1 _ hV _ _ p0, evP_comp1 _ hV _ _ p1,
    evP_pt _ hV, evP_pt _ hV] at h1
  have h2 : comp1 (B.A.act a) (addOf B.G.F P Q) =
      addOf B.G.F (comp1 (B.A.act a) P) (comp1 (B.A.act a) Q) := h1
  have h3 := congrArg (mapP (algebraMap R k)) h2
  rw [baseChange_comp1 _ _ _ (gp_addOf _ B.G.const _ _ hP hQ), baseChange_addOf _ _ _ _ hP hQ,
    baseChange_addOf _ _ _ _ (hc hP) (hc hQ), baseChange_comp1 _ _ _ hP, baseChange_comp1 _ _ _ hQ] at h3
  exact h3

theorem act_foldr (a : O) {ι : Type} {g : ι → Pt k m d} (hg : ∀ b, IsBase R (g b)) (L : List ι) :
    comp1 (B.actK k a) (L.foldr (fun b acc => addOf (B.FK k) (g b) acc) 0) =
      L.foldr (fun b acc => addOf (B.FK k) (comp1 (B.actK k a) (g b)) acc) 0 := by
  induction L with
  | nil => exact gt_comp1_zero _ (gp_act B a)
  | cons b L ih => rw [List.foldr_cons, List.foldr_cons, act_add B a (hg b) (isBase_foldr B hg L), ih]

end Points

section Gauge

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
  {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k] {B : FB R d O} {h : PS k 2 d} {m : ℕ}

theorem const_gauge (hh : B.IsCanonGauge k h) : constantCoeff h = 0 := by
  have := congrArg constantCoeff hh.ax0
  rwa [gt_const_ev_eq _ (pair_points_zero_constant gp_zero₂ (gp_pt 0)), map_zero] at this

theorem gauge_zero_left (hh : B.IsCanonGauge k h) {Q : Pt k m d} (hQ : GP Q) : ev ![0, Q] h = 0 := by
  have := congrArg (ev ![Q]) hh.ax0
  rwa [formalSubst_single_of_formalSubst_two _ hQ _ _ gp_zero₂ (gp_pt 0), formalComp_zero_left_point _ hQ, gt_comp1_pt _ hQ,
    gt_ev_zero _ (single_point_zero_constant hQ)] at this

theorem gauge_zero_right (hh : B.IsCanonGauge k h) {Q : Pt k m d} (hQ : GP Q) : ev ![Q, 0] h = 0 := by
  have := congrArg (ev ![Q]) hh.ax1
  rwa [formalSubst_single_of_formalSubst_two _ hQ _ _ (gp_pt 0) gp_zero₂, formalComp_zero_left_point _ hQ, gt_comp1_pt _ hQ,
    gt_ev_zero _ (single_point_zero_constant hQ)] at this

theorem small_balanced (hh : B.IsCanonGauge k h) (a : O) {P Q : Pt k m d} (hP : IsBase R P)
    (hQ : IsBase R Q) :
    Small R (ev ![comp1 (B.actK k a) P, Q] h - ev ![P, comp1 (B.actK k (star a)) Q] h) := by
  have p0 : GP (pt k (n := 2) d 0) := gp_pt 0
  have p1 : GP (pt k (n := 2) d 1) := gp_pt 1
  have c0 := pair_points_zero_constant (gp_comp1 _ _ (gp_act B a) p0) p1
  have c1 := pair_points_zero_constant p0 (gp_comp1 _ _ (gp_act B (star a)) p1)
  have w1 : constantCoeff (B.ad a) = 1 := by
    rw [← gt_const_ev_eq _ (pair_points_zero_constant (gp_zero₂ (n := 1)) (gp_pt 0)), B.adjoint_zero_fst, map_one]
  have key := Small.subst (isBase2 hP hQ) ⟨by
    rw [map_sub, gt_const_ev_eq _ c0, gt_const_ev_eq _ c1, sub_self], _, w1, hh.ad a⟩
  have hV := pair_points_zero_constant hP.gp hQ.gp
  rw [gt_ev_sub _ hV, gt_ev_ev' _ _ hV c0, gt_ev_ev' _ _ hV c1, eval_pair_points, eval_pair_points,
    evP_comp1 _ hV _ _ p0, evP_comp1 _ hV _ _ p1, evP_pt _ hV, evP_pt _ hV] at key
  exact key

theorem small_add_left (hh : B.IsCanonGauge k h) {P P' Q : Pt k m d} (hP : IsBase R P) (hP' : IsBase R P')
    (hQ : IsBase R Q) :
    Small R (ev ![P, Q] h + ev ![P', Q] h - ev ![addOf (B.FK k) P P', Q] h) := by
  have p0 : GP (pt k (n := 3) d 0) := gp_pt 0
  have p1 : GP (pt k (n := 3) d 1) := gp_pt 1
  have p2 : GP (pt k (n := 3) d 2) := gp_pt 2
  have c0 := pair_points_zero_constant p0 p2
  have c1 := pair_points_zero_constant p1 p2
  have c2 := pair_points_zero_constant (gp_addOf _ (gp_law B) _ _ p0 p1) p2
  have w1 : constantCoeff B.ph1 = 1 := by
    rw [← gt_const_ev_eq _ (triple_points_zero_constant (gp_zero₂ (n := 2)) (gp_pt 0) (gp_pt 1)), B.cocycleLeft_zero_fst, map_one]
  have key := Small.subst (isBase3 hP hP' hQ) ⟨by
    rw [map_sub, map_add, gt_const_ev_eq _ c0, gt_const_ev_eq _ c1, gt_const_ev_eq _ c2, const_gauge hh,
      add_zero, sub_self], _, w1, hh.ph1⟩
  have hV := triple_points_zero_constant hP.gp hP'.gp hQ.gp
  rw [gt_ev_sub _ hV, gt_ev_add _ hV, gt_ev_ev' _ _ hV c0, gt_ev_ev' _ _ hV c1, gt_ev_ev' _ _ hV c2,
    eval_pair_points, eval_pair_points, eval_pair_points, evP_addOf _ hV _ _ _ p0 p1, evP_pt _ hV, evP_pt _ hV,
    evP_pt _ hV] at key
  exact key

theorem small_add_right (hh : B.IsCanonGauge k h) {P Q Q' : Pt k m d} (hP : IsBase R P) (hQ : IsBase R Q)
    (hQ' : IsBase R Q') :
    Small R (ev ![P, Q] h + ev ![P, Q'] h - ev ![P, addOf (B.FK k) Q Q'] h) := by
  have p0 : GP (pt k (n := 3) d 0) := gp_pt 0
  have p1 : GP (pt k (n := 3) d 1) := gp_pt 1
  have p2 : GP (pt k (n := 3) d 2) := gp_pt 2
  have c0 := pair_points_zero_constant p0 p1
  have c1 := pair_points_zero_constant p0 p2
  have c2 := pair_points_zero_constant p0 (gp_addOf _ (gp_law B) _ _ p1 p2)
  have w1 : constantCoeff B.ph2 = 1 := by
    rw [← gt_const_ev_eq _ (triple_points_zero_constant (gp_zero₂ (n := 2)) (gp_pt 0) (gp_pt 1)), B.cocycleRight_zero_fst, map_one]
  have key := Small.subst (isBase3 hP hQ hQ') ⟨by
    rw [map_sub, map_add, gt_const_ev_eq _ c0, gt_const_ev_eq _ c1, gt_const_ev_eq _ c2, const_gauge hh,
      add_zero, sub_self], _, w1, hh.ph2⟩
  have hV := triple_points_zero_constant hP.gp hQ.gp hQ'.gp
  rw [gt_ev_sub _ hV, gt_ev_add _ hV, gt_ev_ev' _ _ hV c0, gt_ev_ev' _ _ hV c1, gt_ev_ev' _ _ hV c2,
    eval_pair_points, eval_pair_points, eval_pair_points, evP_addOf _ hV _ _ _ p1 p2, evP_pt _ hV, evP_pt _ hV,
    evP_pt _ hV] at key
  exact key

theorem small_foldr_left (hh : B.IsCanonGauge k h) {ι : Type} {g : ι → Pt k m d} (hg : ∀ b, IsBase R (g b))
    {Q : Pt k m d} (hQ : IsBase R Q) (L : List ι) :
    Small R (ev ![L.foldr (fun b acc => addOf (B.FK k) (g b) acc) 0, Q] h -
      (L.map fun b => ev ![g b, Q] h).sum) := by
  induction L with
  | nil => exact small_zero.congr (by rw [List.foldr_nil, gauge_zero_left hh hQ.gp]; simp)
  | cons b L ih =>
    refine (ih.add (small_add_left hh (hg b) (isBase_foldr B hg L) hQ).neg).congr ?_
    rw [List.foldr_cons, List.map_cons, List.sum_cons]
    ring

theorem small_foldr_right (hh : B.IsCanonGauge k h) {ι : Type} {g : ι → Pt k m d} (hg : ∀ b, IsBase R (g b))
    {P : Pt k m d} (hP : IsBase R P) (L : List ι) :
    Small R (ev ![P, L.foldr (fun b acc => addOf (B.FK k) (g b) acc) 0] h -
      (L.map fun b => ev ![P, g b] h).sum) := by
  induction L with
  | nil => exact small_zero.congr (by rw [List.foldr_nil, gauge_zero_right hh hP.gp]; simp)
  | cons b L ih =>
    refine (ih.add (small_add_right hh hP (hg b) (isBase_foldr B hg L)).neg).congr ?_
    rw [List.foldr_cons, List.map_cons, List.sum_cons]
    ring

theorem small_sum_scalar (hh : B.IsCanonGauge k h) {ι : Type} (s : Finset ι) (c : ι → O) {P Q : Pt k m d}
    (hP : IsBase R P) (hQ : IsBase R Q) :
    Small R (∑ i ∈ s, ev ![P, comp1 (B.actK k (c i)) Q] h - ev ![P, comp1 (B.actK k (∑ i ∈ s, c i)) Q] h) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have := small_add_right hh hP (hQ.act B 0) (hQ.act B 0)
    rw [← add_act B 0 0 hQ.gp, add_zero] at this
    refine this.neg.congr ?_
    rw [Finset.sum_empty, Finset.sum_empty]
    ring
  | insert i s hi ih =>
    have := small_add_right hh hP (hQ.act B (c i)) (hQ.act B (∑ i ∈ s, c i))
    rw [← add_act B _ _ hQ.gp] at this
    refine (ih.add this).congr ?_
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    ring

theorem small_column (hh : B.IsCanonGauge k h) (w0 : O) (y : Fin m → O) :
    Small R (ev (n := m) ![(List.finRange m).foldr
        (fun b acc => addOf (B.FK k) (comp1 (B.actK k (y b)) (pt k d b)) acc) 0] (B.hL k h w0) -
      ∑ b : Fin m, ∑ b' : Fin m,
        ev (n := m) ![pt k d b, comp1 (B.actK k (w0 * (star (y b) * y b'))) (pt k d b')] h) := by
  have hg : ∀ b, IsBase R (comp1 (B.actK k (y b)) (pt k (n := m) d b)) := fun b => (isBase_pt b).act B _
  have hS := isBase_foldr B hg (List.finRange m)
  rw [FB.hL, gt_comp1_pt_right, formalSubst_single_of_formalSubst_two _ hS.gp _ _ (gp_pt 0) (gp_act B w0), gt_comp1_pt _ hS.gp]
  have h1 := small_foldr_left hh hg (hS.act B w0) (List.finRange m)
  rw [← Fin.sum_univ_def] at h1
  refine h1.trans (Small.sum_sub _ fun b => ?_)
  refine (small_balanced hh (y b) (isBase_pt b) (hS.act B w0)).trans ?_
  rw [act_act B _ _ hS.gp, act_foldr B _ hg]
  have h2 := small_foldr_right hh (fun b' => (hg b').act B (star (y b) * w0)) (isBase_pt b) (List.finRange m)
  rw [← Fin.sum_univ_def] at h2
  refine h2.congr ?_
  congr 1
  refine Finset.sum_congr rfl fun b' _ => ?_
  rw [act_act B _ _ (gp_pt b'), show star (y b) * w0 * y b' = w0 * (star (y b) * y b') by ring]

end Gauge

end GlobalTheory.MatrixGauge

namespace GlobalTheory

open MatrixGauge

theorem exists_integral_unit_matrix_gauge :
    ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h : PS k 2 d), B.IsCanonGauge k h → ∀ (w0 : O) (m n : ℕ) (x : Fin m → Fin n → O), ∃ U : PS R m d, constantCoeff U = 1 ∧ FB.toK k U = FB.expS k ((∑ j : Fin n, ev (n := m) ![(List.finRange m).foldr (fun b acc => addOf (B.FK k) (comp1 (B.actK k (x b j)) (pt k d b)) acc) 0] (B.hL k h w0)) - ∑ b : Fin m, ∑ b' : Fin m, ev (n := m) ![pt k d b, comp1 (B.actK k (w0 * ∑ j : Fin n, star (x b j) * x b' j)) (pt k d b')] h) := by
  intro R _ d O _ _ k _ _ _ B h hh w0 m n x
  have h1 := Small.sum_sub (Finset.univ : Finset (Fin n)) fun j => small_column hh w0 fun b => x b j
  refine (h1.trans ?_).2
  rw [Finset.sum_comm]
  refine Small.sum_sub _ fun b => ?_
  rw [Finset.sum_comm]
  refine Small.sum_sub _ fun b' => ?_
  rw [Finset.mul_sum]
  exact small_sum_scalar hh _ _ (isBase_pt b) (isBase_pt b')

end GlobalTheory
