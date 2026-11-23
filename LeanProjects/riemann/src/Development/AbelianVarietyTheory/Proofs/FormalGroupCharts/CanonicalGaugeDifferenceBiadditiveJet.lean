import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.AdditionLawSecondIdentity
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.JetEqFormalExpIffAndExistsLog
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FormalChartJetRelUnitOneOnAxes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GaugeTrans

set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (transF IsInvPair)
open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open MvPowerSeries

namespace GlobalTheory.ChartCmp.GaugeDiff

section Map
variable {R k : Type} [CommRing R] [CommRing k] {d : ℕ} (β : R →+* k)

def mapPt {n : ℕ} (a : Pt R n d) : Pt k n d := fun i => MvPowerSeries.map β (a i)

theorem map_ev {m n : ℕ} (a : Fin m → Pt R n d) (ha : ∀ j, GP (a j)) (f : PS R m d) :
    MvPowerSeries.map β (ev a f) = ev (fun j => mapPt β (a j)) (MvPowerSeries.map β f) :=
  MvPowerSeries.map_subst (gt_hasSubst a ha) f

theorem map_ev1 {n : ℕ} (a : Pt R n d) (ha : GP a) (f : PS R 1 d) :
    MvPowerSeries.map β (ev ![a] f) = ev ![mapPt β a] (MvPowerSeries.map β f) := by
  rw [map_ev β _ (single_point_zero_constant ha)]
  congr 1
  funext j; fin_cases j; rfl

theorem map_ev2 {n : ℕ} (a b : Pt R n d) (ha : GP a) (hb : GP b) (f : PS R 2 d) :
    MvPowerSeries.map β (ev ![a, b] f) = ev ![mapPt β a, mapPt β b] (MvPowerSeries.map β f) := by
  rw [map_ev β _ (pair_points_zero_constant ha hb)]
  congr 1
  funext j; fin_cases j <;> rfl

theorem map_ev3 {n : ℕ} (a b c : Pt R n d) (ha : GP a) (hb : GP b) (hc : GP c) (f : PS R 3 d) :
    MvPowerSeries.map β (ev ![a, b, c] f) = ev ![mapPt β a, mapPt β b, mapPt β c] (MvPowerSeries.map β f) := by
  rw [map_ev β _ (triple_points_zero_constant ha hb hc)]
  congr 1
  funext j; fin_cases j <;> rfl

theorem constantCoeff_mapPt_eq_zero {n : ℕ} (a : Pt R n d) (ha : GP a) : GP (mapPt β a) := fun i => by
  simp [mapPt, MvPowerSeries.constantCoeff_map, ha i]

theorem mapPt_pt {n : ℕ} (j : Fin n) : mapPt β (pt R d j) = pt k d j := by
  funext i; simp [mapPt, pt]

theorem mapPt_zero {n : ℕ} : mapPt β (0 : Pt R n d) = 0 := by
  funext i; simp [mapPt]

theorem mapPt_comp1 {n : ℕ} (φ : Pt R 1 d) (a : Pt R n d) (ha : GP a) :
    mapPt β (comp1 φ a) = comp1 (mapPt β φ) (mapPt β a) :=
  funext fun i => map_ev1 β a ha (φ i)

theorem mapPt_addOf {n : ℕ} (F : Fin d → PS R 2 d) (a b : Pt R n d) (ha : GP a) (hb : GP b) :
    mapPt β (addOf F a b) = addOf (mapPt β F) (mapPt β a) (mapPt β b) :=
  funext fun i => map_ev2 β a b ha hb (F i)

theorem jeq_map {σ : Type} {m : ℕ} {f g : MvPowerSeries σ R} (h : JEq m f g) :
    JEq m (MvPowerSeries.map β f) (MvPowerSeries.map β g) := fun e he => by
  rw [MvPowerSeries.coeff_map, MvPowerSeries.coeff_map, h e he]

end Map

section Ring
variable {k : Type} [CommRing k] {d : ℕ}

theorem jeq_of_sub {σ : Type} {m : ℕ} {f g u v : MvPowerSeries σ k} (h : JEq m f g) (e : u - v = f - g) :
    JEq m u v := fun x hx => by
  have := congrArg (MvPowerSeries.coeff x) e
  rw [map_sub, map_sub, h x hx, sub_self] at this
  exact sub_eq_zero.1 this

theorem jeq_of_sub' {σ : Type} {m : ℕ} {f g u v : MvPowerSeries σ k} (h : JEq m f g) (e : u - v = g - f) :
    JEq m u v :=
  jeq_of_sub (f := g) (g := f) (fun x hx => (h x hx).symm) e

theorem coordinateChange_comp1_transported_addOf {n : ℕ} {φ φi : Pt k 1 d} (hinv : IsInvPair φ φi) (F F' : Fin d → PS k 2 d) (hBF : GP F)
    (hF : ∀ i, F' i = transF F φ φi i) (a b : Pt k n d) (ha : GP a) (hb : GP b) :
    comp1 φ (addOf F' a b) = addOf F (comp1 φ a) (comp1 φ b) := by
  have hφ : GP φ := hinv.1
  have hp : ∀ {n : ℕ} (j : Fin n), GP (pt k (n := n) d j) := fun j => gp_pt j
  have hcφ : ∀ {n : ℕ} (a : Pt k n d), GP a → GP (comp1 φ a) := fun a ha => gp_comp1 φ a hφ ha
  have hAd : GP (addOf F (comp1 φ (pt k (n := 2) d 0)) (comp1 φ (pt k (n := 2) d 1))) :=
    gp_addOf _ hBF _ _ (hcφ _ (hp 0)) (hcφ _ (hp 1))
  have e : addOf F' a b = comp1 φi (addOf F (comp1 φ a) (comp1 φ b)) := by
    funext i
    change ev ![a, b] (F' i) = ev ![addOf F (comp1 φ a) (comp1 φ b)] (φi i)
    rw [hF i]
    change ev ![a, b] (ev ![addOf F (comp1 φ (pt k (n := 2) d 0)) (comp1 φ (pt k (n := 2) d 1))]
      (φi i)) = _
    rw [gt_ev_ev' ![a, b] _ (pair_points_zero_constant ha hb) (single_point_zero_constant hAd)]
    congr 1
    funext j
    fin_cases j
    change evP ![a, b] (addOf F (comp1 φ (pt k d 0)) (comp1 φ (pt k d 1))) = _
    rw [evP_addOf _ (pair_points_zero_constant ha hb) _ _ _ (hcφ _ (hp 0)) (hcφ _ (hp 1)),
      evP_comp1 _ (pair_points_zero_constant ha hb) φ _ (hp 0), evP_comp1 _ (pair_points_zero_constant ha hb) φ _ (hp 1),
      evP_pt _ (pair_points_zero_constant ha hb), evP_pt _ (pair_points_zero_constant ha hb)]
    rfl
  rw [e, gt_comp_inv hinv _ (gp_addOf _ hBF _ _ (hcφ _ ha) (hcφ _ hb))]

theorem coordinateChange_comp1_intertwines_action {n : ℕ} {φ φi : Pt k 1 d} (hinv : IsInvPair φ φi) (A A' : Pt k 1 d) (hAa : GP A)
    (hA : A' = comp1 φi (comp1 A φ)) (x : Pt k n d) (hx : GP x) :
    comp1 φ (comp1 A' x) = comp1 A (comp1 φ x) := by
  have hφ : GP φ := hinv.1
  rw [hA, gt_comp1_comp1 φi _ (gp_comp1 _ φ hAa hφ) x hx, gt_comp1_comp1 A φ hφ x hx,
    gt_comp_inv hinv _ (gp_comp1 _ _ hAa (gp_comp1 _ _ hφ hx))]

theorem germEv_germEv_two_points {m n : ℕ} (V : Fin m → Pt k n d) (hV : ∀ j, GP (V j)) (a b : Pt k m d) (ha : GP a) (hb : GP b)
    (f : PS k 2 d) : ev V (ev ![a, b] f) = ev ![evP V a, evP V b] f := by
  rw [gt_ev_ev' V _ hV (pair_points_zero_constant ha hb), eval_pair_points]

theorem ev_trans {n : ℕ} (φ : Pt k 1 d) (hφ : GP φ) (h : PS k 2 d) (a b : Pt k n d) (ha : GP a) (hb : GP b) :
    ev ![a, b] (ev ![comp1 φ (pt k (n := 2) d 0), comp1 φ (pt k (n := 2) d 1)] h) =
      ev ![comp1 φ a, comp1 φ b] h := by
  rw [germEv_germEv_two_points _ (pair_points_zero_constant ha hb) _ _ (gp_comp1 _ _ hφ (gp_pt 0)) (gp_comp1 _ _ hφ (gp_pt 1)),
    evP_comp1 _ (pair_points_zero_constant ha hb) φ _ (gp_pt 0),
    evP_comp1 _ (pair_points_zero_constant ha hb) φ _ (gp_pt 1), evP_pt _ (pair_points_zero_constant ha hb), evP_pt _ (pair_points_zero_constant ha hb)]
  rfl

theorem ev_diff {n : ℕ} (φ : Pt k 1 d) (hφ : GP φ) (h h' lam : PS k 2 d) (a b : Pt k n d) (ha : GP a) (hb : GP b) :
    ev ![a, b] (h' - ev ![comp1 φ (pt k (n := 2) d 0), comp1 φ (pt k (n := 2) d 1)] h - lam) =
      ev ![a, b] h' - ev ![comp1 φ a, comp1 φ b] h - ev ![a, b] lam := by
  rw [gt_ev_sub _ (pair_points_zero_constant ha hb), gt_ev_sub _ (pair_points_zero_constant ha hb), ev_trans φ hφ h a b ha hb]

variable [Algebra ℚ k]

theorem expS_zero {n : ℕ} : FB.expS k (0 : PS k n d) = 1 := by
  unfold FB.expS
  ext e
  rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero (by simp)), finsum_eq_single _ 0]
  · simp
  · intro n hn
    simp [hn]

theorem jeq_log {n m : ℕ} {A B C D : PS k n d} (hA : constantCoeff A = 0) (hB : constantCoeff B = 0)
    (hC : constantCoeff C = 0) (hD : constantCoeff D = 0)
    (h : JEq m (FB.expS k A * FB.expS k B) (FB.expS k C * FB.expS k D)) : JEq m (A + B) (C + D) := by
  rw [← gt_expS_add _ _ hA hB, ← gt_expS_add _ _ hC hD] at h
  exact ((GlobalTheory.ChartCmp.jeq_expS_iff_and_exists_log k n d m).1 _ _ (by simp [hA, hB]) (by simp [hC, hD])).2 h

end Ring

theorem biadd_gauge_diff (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (m : ℕ)
    (B B' : FB R d O) (φ φi : Pt R 1 d) (ε : PS R 2 d) (J : JRel m B B' φ φi ε)
    (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (h h' lam : PS k 2 d)
    (hh : B.IsCanonGauge k h) (hh' : B'.IsCanonGauge k h') (hlam0 : MvPowerSeries.constantCoeff lam = 0)
    (hε : FB.expS k lam = FB.toK k ε) :
    Biadd m B' k (h' - ev (n := 2) ![comp1 (fun i => FB.toK k (φ i)) (pt k (n := 2) d 0),
      comp1 (fun i => FB.toK k (φ i)) (pt k (n := 2) d 1)] h - lam) := by
  set β := algebraMap R k with hβ
  change Biadd m B' k (h' - ev (n := 2) ![comp1 (mapPt β φ) (pt k (n := 2) d 0),
      comp1 (mapPt β φ) (pt k (n := 2) d 1)] h - lam)
  have hε' : MvPowerSeries.map β ε = FB.expS k lam := hε.symm
  have hφ : GP φ := J.inv.1
  have hψ : GP (mapPt β φ) := constantCoeff_mapPt_eq_zero β φ hφ
  have fk : B.FK k = mapPt β B.G.F := rfl
  have fk' : B'.FK k = mapPt β B'.G.F := rfl
  have ak : ∀ a, B.actK k a = mapPt β (B.A.act a) := fun a => rfl
  have ak' : ∀ a, B'.actK k a = mapPt β (B'.A.act a) := fun a => rfl
  have hF : GP B.G.F := B.G.const
  have hF' : GP B'.G.F := B'.G.const
  have hFk := constantCoeff_mapPt_eq_zero β _ hF
  have hFk' := constantCoeff_mapPt_eq_zero β _ hF'
  have hr : ∀ {n : ℕ} (j : Fin n), GP (pt R (n := n) d j) := fun j => gp_pt j
  have hp : ∀ {n : ℕ} (j : Fin n), GP (pt k (n := n) d j) := fun j => gp_pt j
  have hcr : ∀ {n : ℕ} (a : Pt R n d), GP a → GP (comp1 φ a) := fun a ha => gp_comp1 φ a hφ ha
  have hc : ∀ {n : ℕ} (a : Pt k n d), GP a → GP (comp1 (mapPt β φ) a) := fun a ha => gp_comp1 _ a hψ ha
  have hz0 : ∀ {n : ℕ}, GP (0 : Pt k n d) := gp_zero₂
  have hh0 : constantCoeff h = 0 := by
    have := congrArg constantCoeff hh.ax0
    rwa [gt_const_ev_eq _ (pair_points_zero_constant hz0 (hp 0)), map_zero] at this
  have hh0' : constantCoeff h' = 0 := by
    have := congrArg constantCoeff hh'.ax0
    rwa [gt_const_ev_eq _ (pair_points_zero_constant hz0 (hp 0)), map_zero] at this
  have cW : ∀ {n : ℕ} (a b : Pt k n d), GP a → GP b → ∀ f : PS k 2 d, constantCoeff f = 0 →
      constantCoeff (ev ![a, b] f) = 0 := fun a b ha hb f hf => gt_const_ev _ (pair_points_zero_constant ha hb) f hf
  have Gl : ∀ i j : Fin 3, comp1 (mapPt β φ) (addOf (mapPt β B'.G.F) (pt k d i) (pt k d j)) =
      addOf (mapPt β B.G.F) (comp1 (mapPt β φ) (pt k d i)) (comp1 (mapPt β φ) (pt k d j)) := by
    intro i j
    have := congrArg (mapPt β) (coordinateChange_comp1_transported_addOf J.inv B.G.F B'.G.F hF J.law (pt R d i) (pt R d j) (hr i) (hr j))
    rwa [mapPt_comp1 β _ _ (gp_addOf _ hF' _ _ (hr i) (hr j)), mapPt_addOf β _ _ _ (hr i) (hr j),
      mapPt_addOf β _ _ _ (hcr _ (hr i)) (hcr _ (hr j)), mapPt_comp1 β _ _ (hr i), mapPt_comp1 β _ _ (hr j),
      mapPt_pt, mapPt_pt] at this
  have Ha : ∀ (a : O) (i : Fin 2), comp1 (mapPt β φ) (comp1 (mapPt β (B'.A.act a)) (pt k d i)) =
      comp1 (mapPt β (B.A.act a)) (comp1 (mapPt β φ) (pt k d i)) := by
    intro a i
    have := congrArg (mapPt β) (coordinateChange_comp1_intertwines_action J.inv (B.A.act a) (B'.A.act a) (B.A.const a) (J.act a) (pt R d i) (hr i))
    rwa [mapPt_comp1 β _ _ (gp_comp1 _ _ (B'.A.const a) (hr i)), mapPt_comp1 β _ _ (hr i),
      mapPt_comp1 β _ _ (hcr _ (hr i)), mapPt_comp1 β _ _ (hr i), mapPt_pt] at this
  obtain ⟨-, hx0, hx1⟩ := GlobalTheory.ChartCmp.jRel_axes R d O m B B' φ φi ε J
  refine ⟨?ax0, ?ax1, ?ph1, ?ph2, ?sy, ?ad⟩
  · have e := jeq_map β hx0
    rw [map_ev2 β _ _ gp_zero₂ (hr 0), mapPt_zero, mapPt_pt, hε', map_one,
      gt_ev_expS _ (pair_points_zero_constant hz0 (hp 0)) _ hlam0, ← expS_zero] at e
    have e' := ((GlobalTheory.ChartCmp.jeq_expS_iff_and_exists_log k 1 d m).1 _ _ (cW _ _ hz0 (hp 0) _ hlam0) (map_zero _)).2 e
    have t := congrArg (ev ![mapPt β φ]) hh.ax0
    rw [germEv_germEv_two_points _ (single_point_zero_constant hψ) _ _ hz0 (hp 0), evP_zero _ (single_point_zero_constant hψ),
      evP_pt _ (single_point_zero_constant hψ), gt_ev_zero _ (single_point_zero_constant hψ)] at t
    rw [ev_diff _ hψ _ _ _ _ _ hz0 (hp 0), hh'.ax0, gt_comp1_zero _ hψ, gt_comp1_pt_right]
    refine jeq_of_sub' e' ?_
    erw [t]
    ring
  · have e := jeq_map β hx1
    rw [map_ev2 β _ _ (hr 0) gp_zero₂, mapPt_zero, mapPt_pt, hε', map_one,
      gt_ev_expS _ (pair_points_zero_constant (hp 0) hz0) _ hlam0, ← expS_zero] at e
    have e' := ((GlobalTheory.ChartCmp.jeq_expS_iff_and_exists_log k 1 d m).1 _ _ (cW _ _ (hp 0) hz0 _ hlam0) (map_zero _)).2 e
    have t := congrArg (ev ![mapPt β φ]) hh.ax1
    rw [germEv_germEv_two_points _ (single_point_zero_constant hψ) _ _ (hp 0) hz0, evP_zero _ (single_point_zero_constant hψ),
      evP_pt _ (single_point_zero_constant hψ), gt_ev_zero _ (single_point_zero_constant hψ)] at t
    rw [ev_diff _ hψ _ _ _ _ _ (hp 0) hz0, hh'.ax1, gt_comp1_zero _ hψ, gt_comp1_pt_right]
    refine jeq_of_sub' e' ?_
    erw [t]
    ring
  · have hq0 := hp (n := 3) 0
    have hq1 := hp (n := 3) 1
    have hq2 := hp (n := 3) 2
    have hV := triple_points_zero_constant (hc _ hq0) (hc _ hq1) (hc _ hq2)
    have hA := gp_addOf _ hFk _ _ hq0 hq1
    have hA' := gp_addOf _ hFk' _ _ hq0 hq1
    have hA'' := gp_addOf _ hFk _ _ (hc _ hq0) (hc _ hq1)
    have e1 : MvPowerSeries.map β B.ph1 = _ := hh.ph1
    have e2 : MvPowerSeries.map β B'.ph1 = _ := hh'.ph1
    rw [fk] at e1
    rw [fk'] at e2
    have e := jeq_map β J.ph1
    rw [map_mul, map_mul, map_mul, map_ev2 β _ _ (gp_addOf _ hF' _ _ (hr 0) (hr 1)) (hr 2),
      map_ev2 β _ _ (hr 0) (hr 2), map_ev2 β _ _ (hr 1) (hr 2),
      map_ev3 β _ _ _ (hcr _ (hr 0)) (hcr _ (hr 1)) (hcr _ (hr 2)), mapPt_addOf β _ _ _ (hr 0) (hr 1),
      mapPt_comp1 β _ _ (hr 0), mapPt_comp1 β _ _ (hr 1), mapPt_comp1 β _ _ (hr 2), mapPt_pt, mapPt_pt, mapPt_pt,
      hε', e1, e2, gt_ev_expS _ (pair_points_zero_constant hA' hq2) _ hlam0, gt_ev_expS _ (pair_points_zero_constant hq0 hq2) _ hlam0,
      gt_ev_expS _ (pair_points_zero_constant hq1 hq2) _ hlam0, ← gt_expS_add _ _ (cW _ _ hq0 hq2 _ hlam0) (cW _ _ hq1 hq2 _ hlam0),
      gt_ev_expS _ hV _ (by simp [cW _ _ hq0 hq2 _ hh0, cW _ _ hq1 hq2 _ hh0, cW _ _ hA hq2 _ hh0]),
      gt_ev_sub _ hV, gt_ev_add _ hV, germEv_germEv_two_points _ hV _ _ hq0 hq2, germEv_germEv_two_points _ hV _ _ hq1 hq2, germEv_germEv_two_points _ hV _ _ hA hq2,
      evP_addOf _ hV _ _ _ hq0 hq1, evP_pt _ hV, evP_pt _ hV, evP_pt _ hV] at e
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons] at e
    have e' := jeq_log
      (by simp [cW _ _ hq0 hq2 _ hh0', cW _ _ hq1 hq2 _ hh0', cW _ _ hA' hq2 _ hh0'])
      (cW _ _ hA' hq2 _ hlam0)
      (by simp [cW _ _ (hc _ hq0) (hc _ hq2) _ hh0, cW _ _ (hc _ hq1) (hc _ hq2) _ hh0,
        cW _ _ hA'' (hc _ hq2) _ hh0])
      (by simp [cW _ _ hq0 hq2 _ hlam0, cW _ _ hq1 hq2 _ hlam0]) e
    rw [fk', ev_diff _ hψ _ _ _ _ _ hA' hq2, ev_diff _ hψ _ _ _ _ _ hq0 hq2, ev_diff _ hψ _ _ _ _ _ hq1 hq2, Gl]
    refine jeq_of_sub' e' ?_
    ring
  · have hq0 := hp (n := 3) 0
    have hq1 := hp (n := 3) 1
    have hq2 := hp (n := 3) 2
    have hV := triple_points_zero_constant (hc _ hq0) (hc _ hq1) (hc _ hq2)
    have hA := gp_addOf _ hFk _ _ hq1 hq2
    have hA' := gp_addOf _ hFk' _ _ hq1 hq2
    have hA'' := gp_addOf _ hFk _ _ (hc _ hq1) (hc _ hq2)
    have e1 : MvPowerSeries.map β B.ph2 = _ := hh.ph2
    have e2 : MvPowerSeries.map β B'.ph2 = _ := hh'.ph2
    rw [fk] at e1
    rw [fk'] at e2
    have e := jeq_map β J.ph2
    rw [map_mul, map_mul, map_mul, map_ev2 β _ _ (hr 0) (gp_addOf _ hF' _ _ (hr 1) (hr 2)),
      map_ev2 β _ _ (hr 0) (hr 1), map_ev2 β _ _ (hr 0) (hr 2),
      map_ev3 β _ _ _ (hcr _ (hr 0)) (hcr _ (hr 1)) (hcr _ (hr 2)), mapPt_addOf β _ _ _ (hr 1) (hr 2),
      mapPt_comp1 β _ _ (hr 0), mapPt_comp1 β _ _ (hr 1), mapPt_comp1 β _ _ (hr 2), mapPt_pt, mapPt_pt, mapPt_pt,
      hε', e1, e2, gt_ev_expS _ (pair_points_zero_constant hq0 hA') _ hlam0, gt_ev_expS _ (pair_points_zero_constant hq0 hq1) _ hlam0,
      gt_ev_expS _ (pair_points_zero_constant hq0 hq2) _ hlam0, ← gt_expS_add _ _ (cW _ _ hq0 hq1 _ hlam0) (cW _ _ hq0 hq2 _ hlam0),
      gt_ev_expS _ hV _ (by simp [cW _ _ hq0 hq1 _ hh0, cW _ _ hq0 hq2 _ hh0, cW _ _ hq0 hA _ hh0]),
      gt_ev_sub _ hV, gt_ev_add _ hV, germEv_germEv_two_points _ hV _ _ hq0 hq1, germEv_germEv_two_points _ hV _ _ hq0 hq2, germEv_germEv_two_points _ hV _ _ hq0 hA,
      evP_addOf _ hV _ _ _ hq1 hq2, evP_pt _ hV, evP_pt _ hV, evP_pt _ hV] at e
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons] at e
    have e' := jeq_log
      (by simp [cW _ _ hq0 hq1 _ hh0', cW _ _ hq0 hq2 _ hh0', cW _ _ hq0 hA' _ hh0'])
      (cW _ _ hq0 hA' _ hlam0)
      (by simp [cW _ _ (hc _ hq0) (hc _ hq1) _ hh0, cW _ _ (hc _ hq0) (hc _ hq2) _ hh0,
        cW _ _ (hc _ hq0) hA'' _ hh0])
      (by simp [cW _ _ hq0 hq1 _ hlam0, cW _ _ hq0 hq2 _ hlam0]) e
    rw [fk', ev_diff _ hψ _ _ _ _ _ hq0 hA', ev_diff _ hψ _ _ _ _ _ hq0 hq1, ev_diff _ hψ _ _ _ _ _ hq0 hq2, Gl]
    refine jeq_of_sub' e' ?_
    ring
  · have hq0 := hp (n := 2) 0
    have hq1 := hp (n := 2) 1
    have hV := pair_points_zero_constant (hc _ hq0) (hc _ hq1)
    have e1 : MvPowerSeries.map β B.sy = _ := hh.sy
    have e2 : MvPowerSeries.map β B'.sy = _ := hh'.sy
    have e := jeq_map β J.sy
    rw [map_mul, map_mul, map_ev2 β _ _ (hr 1) (hr 0), map_ev2 β _ _ (hcr _ (hr 0)) (hcr _ (hr 1)),
      mapPt_comp1 β _ _ (hr 0), mapPt_comp1 β _ _ (hr 1), mapPt_pt, mapPt_pt,
      hε', e1, e2, gt_ev_expS _ (pair_points_zero_constant hq1 hq0) _ hlam0,
      gt_ev_expS _ hV _ (by simp [cW _ _ hq1 hq0 _ hh0, hh0]),
      gt_ev_sub _ hV, germEv_germEv_two_points _ hV _ _ hq1 hq0, evP_pt _ hV, evP_pt _ hV] at e
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at e
    have e' := jeq_log
      (by simp [cW _ _ hq1 hq0 _ hh0', hh0']) hlam0
      (by simp [cW _ _ (hc _ hq0) (hc _ hq1) _ hh0, cW _ _ (hc _ hq1) (hc _ hq0) _ hh0])
      (cW _ _ hq1 hq0 _ hlam0) e
    rw [ev_diff _ hψ _ _ _ _ _ hq1 hq0]
    refine jeq_of_sub e' ?_
    ring
  · intro a
    have hq0 := hp (n := 2) 0
    have hq1 := hp (n := 2) 1
    have hV := pair_points_zero_constant (hc _ hq0) (hc _ hq1)
    have hB'a : GP (B'.A.act a) := B'.A.const a
    have hB's : GP (B'.A.act (star a)) := B'.A.const (star a)
    have hBa := constantCoeff_mapPt_eq_zero β _ (show GP (B.A.act a) from B.A.const a)
    have hBs := constantCoeff_mapPt_eq_zero β _ (show GP (B.A.act (star a)) from B.A.const (star a))
    have hx0 := gp_comp1 _ _ (constantCoeff_mapPt_eq_zero β _ hB'a) hq0
    have hx1 := gp_comp1 _ _ (constantCoeff_mapPt_eq_zero β _ hB's) hq1
    have hy0 := gp_comp1 _ _ hBa hq0
    have hy1 := gp_comp1 _ _ hBs hq1
    have hw0 := gp_comp1 _ _ hBa (hc _ hq0)
    have hw1 := gp_comp1 _ _ hBs (hc _ hq1)
    have e1 : MvPowerSeries.map β (B.ad a) = _ := hh.ad a
    have e2 : MvPowerSeries.map β (B'.ad a) = _ := hh'.ad a
    rw [ak, ak] at e1
    rw [ak', ak'] at e2
    have e := jeq_map β (J.ad a)
    rw [map_mul, map_mul, map_ev2 β _ _ (hr 0) (gp_comp1 _ _ hB's (hr 1)),
      map_ev2 β _ _ (gp_comp1 _ _ hB'a (hr 0)) (hr 1), map_ev2 β _ _ (hcr _ (hr 0)) (hcr _ (hr 1)),
      mapPt_comp1 β φ _ (hr 0), mapPt_comp1 β φ _ (hr 1), mapPt_comp1 β _ _ (hr 0), mapPt_comp1 β _ _ (hr 1),
      mapPt_pt, mapPt_pt,
      hε', e1, e2, gt_ev_expS _ (pair_points_zero_constant hq0 hx1) _ hlam0, gt_ev_expS _ (pair_points_zero_constant hx0 hq1) _ hlam0,
      gt_ev_expS _ hV _ (by simp [cW _ _ hy0 hq1 _ hh0, cW _ _ hq0 hy1 _ hh0]),
      gt_ev_sub _ hV, germEv_germEv_two_points _ hV _ _ hy0 hq1, germEv_germEv_two_points _ hV _ _ hq0 hy1, evP_comp1 _ hV _ _ hq0,
      evP_comp1 _ hV _ _ hq1, evP_pt _ hV, evP_pt _ hV] at e
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at e
    have e' := jeq_log
      (by simp [cW _ _ hx0 hq1 _ hh0', cW _ _ hq0 hx1 _ hh0']) (cW _ _ hq0 hx1 _ hlam0)
      (by simp [cW _ _ hw0 (hc _ hq1) _ hh0, cW _ _ (hc _ hq0) hw1 _ hh0])
      (cW _ _ hx0 hq1 _ hlam0) e
    rw [ak', ak', ev_diff _ hψ _ _ _ _ _ hx0 hq1, ev_diff _ hψ _ _ _ _ _ hq0 hx1, Ha, Ha]
    refine jeq_of_sub e' ?_
    ring

end GlobalTheory.ChartCmp.GaugeDiff
