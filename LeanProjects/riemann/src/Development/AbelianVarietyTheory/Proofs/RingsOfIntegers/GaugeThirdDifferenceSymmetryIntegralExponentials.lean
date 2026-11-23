import Mathlib
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GaugeTrans

set_option autoImplicit false
noncomputable section
open MvPowerSeries IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
namespace GlobalTheory.PlaceInt.ThetaInt

section
variable {V : Type} [CommRing V] {d : ℕ} (K : Type) [CommRing K] [Algebra ℚ K] [Algebra V K]

def mp {n : ℕ} (b : Pt V n d) : Pt K n d := fun i => FB.toK K (b i)

omit [Algebra ℚ K] in
theorem constantCoeff_baseChange_eq_zero {n : ℕ} {b : Pt V n d} (hb : GP b) : GP (mp K b) := by
  intro i
  show constantCoeff (MvPowerSeries.map (algebraMap V K) (b i)) = 0
  rw [MvPowerSeries.constantCoeff_map, hb i, map_zero]

omit [Algebra ℚ K] in
theorem toK_ev {m n : ℕ} (b : Fin m → Pt V n d) (hb : ∀ j, GP (b j)) (f : PS V m d) :
    FB.toK K (ev b f) = ev (fun j => mp K (b j)) (FB.toK K f) := by
  simp only [ev, FB.toK]
  rw [MvPowerSeries.map_subst (gt_hasSubst b hb)]
  rfl

omit [Algebra ℚ K] in
theorem mp_pt {n : ℕ} (j : Fin n) : mp K (pt V d j) = pt K d j := by
  funext i
  simp [mp, pt, FB.toK]

omit [Algebra ℚ K] in
theorem mp_addOf {n : ℕ} (G : FGLaw V d) (a b : Pt V n d) (ha : GP a) (hb : GP b) :
    mp K (addOf G.F a b) = addOf (G.mapF (algebraMap V K)) (mp K a) (mp K b) := by
  funext i
  show FB.toK K (ev ![a, b] (G.F i)) = ev ![mp K a, mp K b] (FB.toK K (G.F i))
  rw [toK_ev K ![a, b] (pair_points_zero_constant ha hb)]
  congr 1
  funext j
  fin_cases j <;> rfl

omit [Algebra ℚ K] in
theorem mp_comp1 {n : ℕ} (φ : Pt V 1 d) (a : Pt V n d) (ha : GP a) :
    mp K (comp1 φ a) = comp1 (mp K φ) (mp K a) := by
  funext i
  show FB.toK K (ev ![a] (φ i)) = ev ![mp K a] (FB.toK K (φ i))
  rw [toK_ev K ![a] (single_point_zero_constant ha)]
  congr 1
  funext j
  fin_cases j
  rfl

theorem expS_zero {n : ℕ} : FB.expS K (0 : PS K n d) = 1 := by
  rw [FB.expS, PowerSeries.subst_zero_eq_C_constantCoeff, PowerSeries.constantCoeff_exp, map_one, map_one]

theorem cc_expS {n : ℕ} (g : PS K n d) (hg : constantCoeff g = 0) : constantCoeff (FB.expS K g) = 1 := by
  have ha : PowerSeries.HasSubst g := PowerSeries.HasSubst.of_constantCoeff_zero hg
  have e : PowerSeries.exp K = 1 + (PowerSeries.exp K - 1) := by ring
  have h1 : PowerSeries.constantCoeff (PowerSeries.exp K - 1) = 0 := by
    rw [map_sub, PowerSeries.constantCoeff_exp, map_one, sub_self]
  rw [FB.expS, e, PowerSeries.subst_add ha, map_add, PowerSeries.constantCoeff_subst_eq_zero hg _ h1, add_zero,
    ← PowerSeries.coe_substAlgHom ha, map_one, map_one]

variable (V d) in

def intExp (hi : Function.Injective (algebraMap V K)) (n : ℕ) : AddSubgroup (PS K n d) where
  carrier := {g | constantCoeff g = 0 ∧ ∃ u : PS V n d, FB.toK K u = FB.expS K g}
  zero_mem' := ⟨map_zero _, 1, by rw [expS_zero, FB.toK, map_one]⟩
  add_mem' := by
    rintro f g ⟨hf, u, hu⟩ ⟨hg, v, hv⟩
    refine ⟨by rw [map_add, hf, hg, add_zero], u * v, ?_⟩
    rw [gt_expS_add _ _ hf hg, ← hu, ← hv, FB.toK, map_mul]
  neg_mem' := by
    rintro f ⟨hf, u, hu⟩
    have hn : constantCoeff (-f) = 0 := by rw [map_neg, hf, neg_zero]
    have h1 : constantCoeff u = 1 := by
      apply hi
      have := cc_expS K f hf
      rw [← hu] at this
      simpa [FB.toK] using this
    have hU : IsUnit u := by rw [MvPowerSeries.isUnit_iff_constantCoeff, h1]; exact isUnit_one
    obtain ⟨v, hv⟩ := hU.exists_right_inv
    refine ⟨hn, v, ?_⟩
    have e1 : FB.expS K f * FB.expS K (-f) = 1 := by
      rw [← gt_expS_add _ _ hf hn, add_neg_cancel, expS_zero]
    have e2 : FB.toK K v * FB.expS K f = 1 := by
      rw [← hu, FB.toK, FB.toK, ← map_mul, mul_comm, hv, map_one]
    calc FB.toK K v = FB.toK K v * (FB.expS K f * FB.expS K (-f)) := by rw [e1, mul_one]
      _ = _ := by rw [← mul_assoc, e2, one_mul]

theorem ev_mem (hi : Function.Injective (algebraMap V K)) {m n : ℕ} (b : Fin m → Pt V n d) (hb : ∀ j, GP (b j))
    {g : PS K m d} (hg : g ∈ intExp V d K hi m) : ev (fun j => mp K (b j)) g ∈ intExp V d K hi n := by
  obtain ⟨hg0, u, hu⟩ := hg
  have hmb : ∀ j, GP (mp K (b j)) := fun j => constantCoeff_baseChange_eq_zero K (hb j)
  refine ⟨gt_const_ev _ hmb g hg0, ev b u, ?_⟩
  rw [toK_ev K b hb, hu, gt_ev_expS _ hmb g hg0]

variable {O : Type} [CommRing O] [StarRing O] (B : FB V d O) {h : PS K 2 d}

theorem cc_gauge (hh : B.IsCanonGauge K h) : constantCoeff h = 0 := by
  have h1 := congrArg constantCoeff hh.ax0
  rwa [gt_const_ev_eq _ (pair_points_zero_constant gp_zero₂ (gp_pt 0)), map_zero] at h1

omit [Algebra ℚ K] in
theorem cc_FK (i : Fin d) : constantCoeff (B.FK K i) = 0 := by
  show constantCoeff (MvPowerSeries.map (algebraMap V K) (B.G.F i)) = 0
  rw [MvPowerSeries.constantCoeff_map, B.G.const i, map_zero]

def cls (hi : Function.Injective (algebraMap V K)) (h : PS K 2 d) {n : ℕ} (a b : Pt V n d) :
    PS K n d ⧸ intExp V d K hi n :=
  QuotientAddGroup.mk' (intExp V d K hi n) (ev ![mp K a, mp K b] h)

theorem cls_add_left (hi : Function.Injective (algebraMap V K)) (hh : B.IsCanonGauge K h) {n : ℕ}
    (a b c : Pt V n d) (ha : GP a) (hb : GP b) (hc : GP c) :
    cls K hi h (addOf B.G.F a b) c = cls K hi h a c + cls K hi h b c := by
  have hc0 : constantCoeff h = 0 := cc_gauge K B hh
  have g0 : GP (pt K (n := 3) d 0) := gp_pt 0
  have g1 : GP (pt K (n := 3) d 1) := gp_pt 1
  have g2 : GP (pt K (n := 3) d 2) := gp_pt 2
  have g01 : GP (addOf (B.FK K) (pt K (n := 3) d 0) (pt K d 1)) := gp_addOf _ (cc_FK K B) _ _ g0 g1
  have hm : (ev ![pt K d 0, pt K d 2] h + ev ![pt K d 1, pt K d 2] h -
      ev ![addOf (B.FK K) (pt K d 0) (pt K d 1), pt K d 2] h) ∈ intExp V d K hi 3 := by
    refine ⟨?_, B.ph1, hh.ph1⟩
    rw [map_sub, map_add, gt_const_ev _ (pair_points_zero_constant g0 g2) h hc0, gt_const_ev _ (pair_points_zero_constant g1 g2) h hc0,
      gt_const_ev _ (pair_points_zero_constant g01 g2) h hc0, add_zero, sub_zero]
  have hE := ev_mem K hi ![a, b, c] (triple_points_zero_constant ha hb hc) hm
  have hW : (fun j => mp K (![a, b, c] j)) = ![mp K a, mp K b, mp K c] := by
    funext j
    fin_cases j <;> rfl
  have hV := triple_points_zero_constant (constantCoeff_baseChange_eq_zero K ha) (constantCoeff_baseChange_eq_zero K hb) (constantCoeff_baseChange_eq_zero K hc)
  rw [hW, gt_ev_sub _ hV, gt_ev_add _ hV, gt_ev_ev' _ _ hV (pair_points_zero_constant g0 g2), gt_ev_ev' _ _ hV (pair_points_zero_constant g1 g2),
    gt_ev_ev' _ _ hV (pair_points_zero_constant g01 g2), eval_pair_points, eval_pair_points, eval_pair_points, evP_addOf _ hV _ _ _ g0 g1] at hE
  simp only [evP_pt _ hV, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons] at hE
  rw [show addOf (B.FK K) (mp K a) (mp K b) = mp K (addOf B.G.F a b) from (mp_addOf K B.G a b ha hb).symm] at hE
  unfold cls
  rw [← sub_eq_zero, ← map_add, ← map_sub, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff, ← neg_sub]
  exact neg_mem hE

theorem cls_add_right (hi : Function.Injective (algebraMap V K)) (hh : B.IsCanonGauge K h) {n : ℕ}
    (a b c : Pt V n d) (ha : GP a) (hb : GP b) (hc : GP c) :
    cls K hi h a (addOf B.G.F b c) = cls K hi h a b + cls K hi h a c := by
  have hc0 : constantCoeff h = 0 := cc_gauge K B hh
  have g0 : GP (pt K (n := 3) d 0) := gp_pt 0
  have g1 : GP (pt K (n := 3) d 1) := gp_pt 1
  have g2 : GP (pt K (n := 3) d 2) := gp_pt 2
  have g12 : GP (addOf (B.FK K) (pt K (n := 3) d 1) (pt K d 2)) := gp_addOf _ (cc_FK K B) _ _ g1 g2
  have hm : (ev ![pt K d 0, pt K d 1] h + ev ![pt K d 0, pt K d 2] h -
      ev ![pt K d 0, addOf (B.FK K) (pt K d 1) (pt K d 2)] h) ∈ intExp V d K hi 3 := by
    refine ⟨?_, B.ph2, hh.ph2⟩
    rw [map_sub, map_add, gt_const_ev _ (pair_points_zero_constant g0 g1) h hc0, gt_const_ev _ (pair_points_zero_constant g0 g2) h hc0,
      gt_const_ev _ (pair_points_zero_constant g0 g12) h hc0, add_zero, sub_zero]
  have hE := ev_mem K hi ![a, b, c] (triple_points_zero_constant ha hb hc) hm
  have hW : (fun j => mp K (![a, b, c] j)) = ![mp K a, mp K b, mp K c] := by
    funext j
    fin_cases j <;> rfl
  have hV := triple_points_zero_constant (constantCoeff_baseChange_eq_zero K ha) (constantCoeff_baseChange_eq_zero K hb) (constantCoeff_baseChange_eq_zero K hc)
  rw [hW, gt_ev_sub _ hV, gt_ev_add _ hV, gt_ev_ev' _ _ hV (pair_points_zero_constant g0 g1), gt_ev_ev' _ _ hV (pair_points_zero_constant g0 g2),
    gt_ev_ev' _ _ hV (pair_points_zero_constant g0 g12), eval_pair_points, eval_pair_points, eval_pair_points, evP_addOf _ hV _ _ _ g1 g2] at hE
  simp only [evP_pt _ hV, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons] at hE
  rw [show addOf (B.FK K) (mp K b) (mp K c) = mp K (addOf B.G.F b c) from (mp_addOf K B.G b c hb hc).symm] at hE
  unfold cls
  rw [← sub_eq_zero, ← map_add, ← map_sub, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff, ← neg_sub]
  exact neg_mem hE

theorem act_addOf (w : O) {n : ℕ} (a b : Pt V n d) (ha : GP a) (hb : GP b) :
    comp1 (B.A.act w) (addOf B.G.F a b) = addOf B.G.F (comp1 (B.A.act w) a) (comp1 (B.A.act w) b) := by
  have g0 : GP (pt V (n := 2) d 0) := gp_pt 0
  have g1 : GP (pt V (n := 2) d 1) := gp_pt 1
  have hV := pair_points_zero_constant ha hb
  have hact : GP (B.A.act w) := B.A.const w
  have key := congrArg (evP ![a, b]) (B.A.hom w)
  simp only [FGLaw.add] at key
  rw [evP_comp1 _ hV _ _ (gp_addOf _ B.G.const _ _ g0 g1), evP_addOf _ hV _ _ _ g0 g1,
    evP_addOf _ hV _ _ _ (gp_comp1 _ _ hact g0) (gp_comp1 _ _ hact g1),
    evP_comp1 _ hV _ _ g0, evP_comp1 _ hV _ _ g1, evP_pt _ hV, evP_pt _ hV] at key
  simpa using key

omit [Algebra ℚ K] in
theorem ev_hL (h : PS K 2 d) (w : O) {n : ℕ} (a : Pt V n d) (ha : GP a) :
    ev ![mp K a] (B.hL K h w) = ev ![mp K a, mp K (comp1 (B.A.act w) a)] h := by
  have hA : GP (mp K a) := constantCoeff_baseChange_eq_zero K ha
  have hK : GP (B.actK K w) := constantCoeff_baseChange_eq_zero K (B.A.const w)
  have g0 : GP (pt K (n := 1) d 0) := gp_pt 0
  have e : mp K (comp1 (B.A.act w) a) = comp1 (B.actK K w) (mp K a) := mp_comp1 K (B.A.act w) a ha
  rw [e, FB.hL, gt_ev_ev' _ _ (single_point_zero_constant hA) (pair_points_zero_constant g0 (gp_comp1 _ _ hK g0)), eval_pair_points,
    evP_comp1 _ (single_point_zero_constant hA) _ _ g0, evP_pt _ (single_point_zero_constant hA)]
  rfl

theorem exists_theta (hi : Function.Injective (algebraMap V K)) (hh : B.IsCanonGauge K h) (w : O) :
    ∃ Θ : PS V 3 d, IsTheta B K h w Θ := by
  have gpA : ∀ a : Pt V 3 d, GP a → GP (comp1 (B.A.act w) a) := fun a ha => gp_comp1 _ a (B.A.const w) ha
  have gpS : ∀ a b : Pt V 3 d, GP a → GP b → GP (addOf B.G.F a b) :=
    fun a b ha hb => gp_addOf _ B.G.const a b ha hb
  have hLc : ∀ a : Pt V 3 d, GP a → QuotientAddGroup.mk' (intExp V d K hi 3) (ev ![mp K a] (B.hL K h w)) =
      cls K hi h a (comp1 (B.A.act w) a) := by
    intro a ha
    rw [ev_hL K B h w a ha]
    rfl
  have PL : ∀ a b c : Pt V 3 d, GP a → GP b → GP c →
      cls K hi h (addOf B.G.F a b) (comp1 (B.A.act w) c) =
        cls K hi h a (comp1 (B.A.act w) c) + cls K hi h b (comp1 (B.A.act w) c) :=
    fun a b c ha hb hc => cls_add_left K B hi hh a b _ ha hb (gpA c hc)
  have PR : ∀ a b c : Pt V 3 d, GP a → GP b → GP c →
      cls K hi h a (comp1 (B.A.act w) (addOf B.G.F b c)) =
        cls K hi h a (comp1 (B.A.act w) b) + cls K hi h a (comp1 (B.A.act w) c) := by
    intro a b c ha hb hc
    rw [act_addOf B w b c hb hc]
    exact cls_add_right K B hi hh a _ _ ha (gpA b hb) (gpA c hc)
  have es : ∀ a b : Pt V 3 d, GP a → GP b → addOf (B.FK K) (mp K a) (mp K b) = mp K (addOf B.G.F a b) :=
    fun a b ha hb => (mp_addOf K B.G a b ha hb).symm
  have hx : GP (pt V (n := 3) d 0) := gp_pt 0
  have hy : GP (pt V (n := 3) d 1) := gp_pt 1
  have hz : GP (pt V (n := 3) d 2) := gp_pt 2
  have hxy := gpS _ _ hx hy
  have hxz := gpS _ _ hx hz
  have hyz := gpS _ _ hy hz
  have hxyz := gpS _ _ hxy hz
  have hmem : ev ![mp K (addOf B.G.F (addOf B.G.F (pt V d 0) (pt V d 1)) (pt V d 2))] (B.hL K h w)
      - ev ![mp K (addOf B.G.F (pt V d 0) (pt V d 1))] (B.hL K h w)
      - ev ![mp K (addOf B.G.F (pt V d 0) (pt V d 2))] (B.hL K h w)
      - ev ![mp K (addOf B.G.F (pt V d 1) (pt V d 2))] (B.hL K h w)
      + ev ![mp K (pt V d 0)] (B.hL K h w) + ev ![mp K (pt V d 1)] (B.hL K h w)
      + ev ![mp K (pt V (n := 3) d 2)] (B.hL K h w) ∈ intExp V d K hi 3 := by
    rw [← QuotientAddGroup.eq_zero_iff, ← QuotientAddGroup.mk'_apply]
    simp only [map_add, map_sub]
    rw [hLc _ hxyz, hLc _ hxy, hLc _ hxz, hLc _ hyz, hLc _ hx, hLc _ hy, hLc _ hz,
      PL _ _ _ hxy hz hxyz, PL _ _ _ hx hy hxyz, PR _ _ _ hx hxy hz, PR _ _ _ hy hxy hz, PR _ _ _ hz hxy hz,
      PR _ _ _ hx hx hy, PR _ _ _ hy hx hy, PR _ _ _ hz hx hy,
      PL _ _ _ hx hy hxy, PR _ _ _ hx hx hy, PR _ _ _ hy hx hy,
      PL _ _ _ hx hz hxz, PR _ _ _ hx hx hz, PR _ _ _ hz hx hz,
      PL _ _ _ hy hz hyz, PR _ _ _ hy hy hz, PR _ _ _ hz hy hz]
    abel
  obtain ⟨-, u, hu⟩ := hmem
  refine ⟨u, ?_⟩
  unfold IsTheta
  dsimp only
  rw [← mp_pt (V := V) K (0 : Fin 3), ← mp_pt (V := V) K (1 : Fin 3), ← mp_pt (V := V) K (2 : Fin 3),
    es _ _ hx hy, es _ _ hxy hz, es _ _ hx hz, es _ _ hy hz]
  exact hu

private theorem actK_mul_eq_comp1 (a b : O) : B.actK K (a * b) = comp1 (B.actK K a) (B.actK K b) := by
  show mp K (B.A.act (a * b)) = comp1 (mp K (B.A.act a)) (mp K (B.A.act b))
  rw [B.A.mul_act]
  exact mp_comp1 K (B.A.act a) (B.A.act b) (B.A.const b)

theorem exists_iota (hi : Function.Injective (algebraMap V K)) (hh : B.IsCanonGauge K h) (w : O) :
    ∃ jo : PS V 1 d, IsIota B K h w jo := by
  have gpK : ∀ a : O, GP (B.actK K a) := fun a => constantCoeff_baseChange_eq_zero K (B.A.const a)
  have g0 : GP (pt K (n := 2) d 0) := gp_pt 0
  have g1 : GP (pt K (n := 2) d 1) := gp_pt 1
  have hW1 := pair_points_zero_constant (gp_comp1 _ _ (gpK (-1)) g0) g1
  have hW2 := pair_points_zero_constant g0 (gp_comp1 _ _ (gpK (star (-1))) g1)
  have hD : ev ![comp1 (B.actK K (-1)) (pt K d 0), pt K d 1] h -
      ev ![pt K d 0, comp1 (B.actK K (star (-1))) (pt K d 1)] h ∈ intExp V d K hi 2 := by
    refine ⟨?_, B.ad (-1), hh.ad (-1)⟩
    rw [map_sub, gt_const_ev_eq _ hW1, gt_const_ev_eq _ hW2, sub_self]
  have hb : ∀ j, GP (![(pt V d 0 : Pt V 1 d), B.A.act (w * -1)] j) := pair_points_zero_constant (gp_pt 0) (B.A.const _)
  obtain ⟨-, u, hu⟩ := (ev_mem K hi _ hb hD)
  refine ⟨u, ?_⟩
  unfold IsIota
  rw [hu]
  congr 1
  have hW : (fun j => mp K (![(pt V d 0 : Pt V 1 d), B.A.act (w * -1)] j)) =
      ![pt K d 0, B.actK K (w * -1)] := by
    funext j
    fin_cases j
    · exact mp_pt K 0
    · rfl
  have p0 : GP (pt K (n := 1) d 0) := gp_pt 0
  have hV := pair_points_zero_constant p0 (gpK (w * -1))
  have hV1 := single_point_zero_constant (gpK (-1))
  have e1 : B.actK K (w * -1) = comp1 (B.actK K w) (B.actK K (-1)) := actK_mul_eq_comp1 K B w (-1)
  have e2 : comp1 (B.actK K (star (-1))) (B.actK K (w * -1)) = B.actK K w := by
    rw [← actK_mul_eq_comp1 K B]
    congr 1
    rw [star_neg, star_one]
    ring
  rw [hW, gt_ev_sub _ hV, gt_ev_ev' _ _ hV hW1, gt_ev_ev' _ _ hV hW2, eval_pair_points, eval_pair_points,
    evP_comp1 _ hV _ _ g0, evP_comp1 _ hV _ _ g1]
  simp only [evP_pt _ hV, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [e2, gt_comp1_pt_right, FB.hL, gt_ev_ev' _ _ hV1 (pair_points_zero_constant p0 (gp_comp1 _ _ (gpK w) p0)), eval_pair_points,
    evP_comp1 _ hV1 _ _ p0]
  simp only [evP_pt _ hV1, Matrix.cons_val_zero, gt_comp1_pt_right, e1]

end

end GlobalTheory.PlaceInt.ThetaInt

namespace GlobalTheory.PlaceInt

theorem exists_isTheta_and_isIota :
    ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V]
      (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB V d O) (K : Type) [Field K] [Algebra ℚ K] [Algebra V K]
      [IsFractionRing V K] (h : PS K 2 d) (w0 : O), B.IsCanonGauge K h →
      (∃ Θ : PS V 3 d, IsTheta B K h w0 Θ) ∧ ∃ jo : PS V 1 d, IsIota B K h w0 jo := by
  intro V _ _ _ _ _ d O _ _ B K _ _ _ _ h w0 hh
  exact ⟨ThetaInt.exists_theta K B (IsFractionRing.injective V K) hh w0, ThetaInt.exists_iota K B (IsFractionRing.injective V K) hh w0⟩

end GlobalTheory.PlaceInt
