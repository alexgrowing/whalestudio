import Mathlib
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SmallPointsSubstitutionAlgHomSinglePoint
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.GaugeThirdDifferenceSymmetryIntegralExponentials

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
open GlobalTheory.TransUnit
open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing GlobalTheory.PlaceInt.ThetaInt

namespace GlobalTheory.TransUnit.IotaLaw

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V]
  {d : ℕ} {O : Type} [CommRing O] [StarRing O] {B : FB V d O} {n : ℕ}

theorem evA_three (x y z : Sm B n) (hx : GP x.1) (hy : GP y.1) (hz : GP z.1) (f : PS V 3 d) :
    evA ![x, y, z] f = ev ![x.1, y.1, z.1] f := by
  rw [evA_eq_ev]
  · congr 1
    funext j
    fin_cases j <;> rfl
  · intro j i
    fin_cases j
    exacts [hx i, hy i, hz i]

theorem mul_val_of (x y : Sm B n) (hx : GP x.1) (hy : GP y.1) : (x * y).1 = addOf B.G.F x.1 y.1 := by
  rw [Sm.mul_val]
  funext i
  show evV ![x.1, y.1] (B.G.F i) = ev ![x.1, y.1] (B.G.F i)
  rw [← smallPointsSubstitutionAlgHom_two_points, evA_eq_ev]
  · congr 1
    funext j
    fin_cases j <;> rfl
  · intro j k
    fin_cases j
    exacts [hx k, hy k]

theorem compV_of (φ : Pt V 1 d) (x : Sm B n) (hx : GP x.1) : compV φ x.1 = comp1 φ x.1 := by
  funext i
  show evV ![x.1] (φ i) = ev ![x.1] (φ i)
  rw [← smallPointsSubstitutionAlgHom_single_point, evA_eq_ev]
  · congr 1
    funext j
    fin_cases j
    rfl
  · intro j k
    fin_cases j
    exact hx k

theorem constantCoeff_act_eq_zero (o : O) (x : Sm B n) (hx : GP x.1) : GP (Sm.act B o x).1 := by
  rw [Sm.act_val, compV_of _ x hx]
  exact gp_comp1 _ _ (fun i => B.A.const o i) hx

theorem constantCoeff_inv_eq_zero (x : Sm B n) (hx : GP x.1) : GP (x⁻¹).1 := by
  rw [Sm.inv_val, ← Sm.act_val]
  exact constantCoeff_act_eq_zero (-1) x hx

variable (K : Type) [Field K] [Algebra ℚ K] [Algebra V K] {h : PS K 2 d}

omit [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] [Algebra ℚ K] in
theorem mp_zero : mp K (0 : Pt V n d) = 0 := by
  funext i
  simp [mp]

omit [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] in
theorem ev_zero_zero_gp_eq_one_of_ev_zero_pt_pt_eq_one (hh : B.IsCanonGauge K h) (a : Pt K n d) (ha : GP a) : ev ![0, a] h = 0 := by
  obtain ⟨h1, h2, -, -, -, -⟩ := hh
  have hv : ∀ j, GP (![a] j) := single_point_zero_constant ha
  have hw : ∀ j, GP (![(0 : Pt K 1 d), pt K (n := 1) d 0] j) := pair_points_zero_constant gp_zero₂ (gp_pt 0)
  have e := gt_ev_ev' ![a] _ hv hw h
  rw [h1, eval_pair_points, evP_zero _ hv, evP_pt _ hv] at e
  simp only [Matrix.cons_val_zero] at e
  rw [← e, gt_ev_zero _ hv]

omit [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] in
theorem canonicalGauge_eval_zero_right (hh : B.IsCanonGauge K h) (a : Pt K n d) (ha : GP a) : ev ![a, 0] h = 0 := by
  obtain ⟨h1, h2, -, -, -, -⟩ := hh
  have hv : ∀ j, GP (![a] j) := single_point_zero_constant ha
  have hw : ∀ j, GP (![pt K (n := 1) d 0, (0 : Pt K 1 d)] j) := pair_points_zero_constant (gp_pt 0) gp_zero₂
  have e := gt_ev_ev' ![a] _ hv hw h
  rw [h2, eval_pair_points, evP_zero _ hv, evP_pt _ hv] at e
  simp only [Matrix.cons_val_zero] at e
  rw [← e, gt_ev_zero _ hv]

theorem canonicalGauge_first_partial_law_in_field (hh : B.IsCanonGauge K h) (x y z : Sm B n) (hx : GP x.1) (hy : GP y.1) (hz : GP z.1) :
    FB.toK K (evA ![x, y, z] B.ph1) = FB.expS K (ev ![mp K x.1, mp K z.1] h + ev ![mp K y.1, mp K z.1] h
      - ev ![mp K (x * y).1, mp K z.1] h) := by
  have hc : MvPowerSeries.constantCoeff h = 0 := cc_gauge (K := K) (B := B) hh
  obtain ⟨-, -, h3, h4, -, -⟩ := hh
  have hF : ∀ i, MvPowerSeries.constantCoeff (B.FK K i) = 0 := cc_FK (K := K) (B := B)
  have p0 : GP (pt K (n := 3) d 0) := gp_pt 0
  have p1 : GP (pt K (n := 3) d 1) := gp_pt 1
  have p2 : GP (pt K (n := 3) d 2) := gp_pt 2
  have pa : GP (addOf (B.FK K) (pt K (n := 3) d 0) (pt K d 1)) := gp_addOf _ hF _ _ p0 p1
  have hX : ∀ j, GP (![mp K x.1, mp K y.1, mp K z.1] j) := triple_points_zero_constant (constantCoeff_baseChange_eq_zero K hx) (constantCoeff_baseChange_eq_zero K hy) (constantCoeff_baseChange_eq_zero K hz)
  have hv : (fun j => mp K (![x.1, y.1, z.1] j)) = ![mp K x.1, mp K y.1, mp K z.1] := by
    funext j
    fin_cases j <;> rfl
  rw [evA_three x y z hx hy hz, toK_ev K _ (triple_points_zero_constant hx hy hz), h3, hv]
  rw [gt_ev_expS _ hX]
  · congr 1
    rw [gt_ev_sub _ hX, gt_ev_add _ hX, gt_ev_ev' _ _ hX (pair_points_zero_constant p0 p2), gt_ev_ev' _ _ hX (pair_points_zero_constant p1 p2),
      gt_ev_ev' _ _ hX (pair_points_zero_constant pa p2), eval_pair_points, eval_pair_points, eval_pair_points, evP_addOf _ hX _ _ _ p0 p1,
      evP_pt _ hX, evP_pt _ hX, evP_pt _ hX, mul_val_of x y hx hy, mp_addOf K B.G _ _ hx hy]
    rfl
  · rw [map_sub, map_add, gt_const_ev_eq _ (pair_points_zero_constant p0 p2), gt_const_ev_eq _ (pair_points_zero_constant p1 p2),
      gt_const_ev_eq _ (pair_points_zero_constant pa p2), hc]
    simp

theorem canonicalGauge_second_partial_law_in_field (hh : B.IsCanonGauge K h) (x y z : Sm B n) (hx : GP x.1) (hy : GP y.1) (hz : GP z.1) :
    FB.toK K (evA ![x, y, z] B.ph2) = FB.expS K (ev ![mp K x.1, mp K y.1] h + ev ![mp K x.1, mp K z.1] h
      - ev ![mp K x.1, mp K (y * z).1] h) := by
  have hc : MvPowerSeries.constantCoeff h = 0 := cc_gauge (K := K) (B := B) hh
  obtain ⟨-, -, h3, h4, -, -⟩ := hh
  have hF : ∀ i, MvPowerSeries.constantCoeff (B.FK K i) = 0 := cc_FK (K := K) (B := B)
  have p0 : GP (pt K (n := 3) d 0) := gp_pt 0
  have p1 : GP (pt K (n := 3) d 1) := gp_pt 1
  have p2 : GP (pt K (n := 3) d 2) := gp_pt 2
  have pa : GP (addOf (B.FK K) (pt K (n := 3) d 1) (pt K d 2)) := gp_addOf _ hF _ _ p1 p2
  have hX : ∀ j, GP (![mp K x.1, mp K y.1, mp K z.1] j) := triple_points_zero_constant (constantCoeff_baseChange_eq_zero K hx) (constantCoeff_baseChange_eq_zero K hy) (constantCoeff_baseChange_eq_zero K hz)
  have hv : (fun j => mp K (![x.1, y.1, z.1] j)) = ![mp K x.1, mp K y.1, mp K z.1] := by
    funext j
    fin_cases j <;> rfl
  rw [evA_three x y z hx hy hz, toK_ev K _ (triple_points_zero_constant hx hy hz), h4, hv]
  rw [gt_ev_expS _ hX]
  · congr 1
    rw [gt_ev_sub _ hX, gt_ev_add _ hX, gt_ev_ev' _ _ hX (pair_points_zero_constant p0 p1), gt_ev_ev' _ _ hX (pair_points_zero_constant p0 p2),
      gt_ev_ev' _ _ hX (pair_points_zero_constant p0 pa), eval_pair_points, eval_pair_points, eval_pair_points, evP_addOf _ hX _ _ _ p1 p2,
      evP_pt _ hX, evP_pt _ hX, evP_pt _ hX, mul_val_of y z hy hz, mp_addOf K B.G _ _ hy hz]
    rfl
  · rw [map_sub, map_add, gt_const_ev_eq _ (pair_points_zero_constant p0 p1), gt_const_ev_eq _ (pair_points_zero_constant p0 p2),
      gt_const_ev_eq _ (pair_points_zero_constant p0 pa), hc]
    simp

private theorem eq_of_toK_eq_of_injective (hi : Function.Injective (algebraMap V K)) {m : ℕ} (a b : PS V m d)
    (hab : FB.toK K a = FB.toK K b) : a = b := by
  unfold FB.toK at hab
  refine MvPowerSeries.ext fun k => ?_
  have e := congrArg (MvPowerSeries.coeff k) hab
  rw [MvPowerSeries.coeff_map, MvPowerSeries.coeff_map] at e
  exact hi e

theorem iota_gen (hi : Function.Injective (algebraMap V K)) (hh : B.IsCanonGauge K h) (w0 : O)
    (p₁ p₂ : (PS V 3 d)ˣ) (e₁ : p₁.val = B.ph1) (e₂ : p₂.val = B.ph2) (jo : PS V 1 d) (hj : IsIota B K h w0 jo) :
    jo = (quadN (u3 p₁) (u3 p₂) (Sm.act B w0) (Sm.gen B (0 : Fin 1))).val := by
  unfold IsIota at hj
  set g : Sm B 1 := Sm.gen B 0 with hgdef
  have hg : GP g.1 := gp_pt 0
  have hgi : GP (g⁻¹).1 := constantCoeff_inv_eq_zero g hg
  have hwg : GP (Sm.act B w0 g).1 := constantCoeff_act_eq_zero w0 g hg
  have hwgi : GP ((Sm.act B w0 g)⁻¹).1 := constantCoeff_inv_eq_zero _ hwg
  have hc : MvPowerSeries.constantCoeff h = 0 := cc_gauge (K := K) (B := B) hh
  have c2 : ∀ a b : Pt K 1 d, GP a → GP b → MvPowerSeries.constantCoeff (ev ![a, b] h) = 0 := fun a b ha hb => by
    rw [gt_const_ev_eq _ (pair_points_zero_constant ha hb), hc]
  have hL1 : B.hL K h w0 = ev ![mp K g.1, mp K (Sm.act B w0 g).1] h := by
    have e := ev_hL K B h w0 g.1 hg
    rw [Sm.act_val, compV_of _ g hg, ← e, show mp K g.1 = pt K (n := 1) d 0 from mp_pt K 0, gt_ev_pt_self]
  have ha : mp K (g⁻¹).1 = B.actK K (-1) := by
    rw [Sm.inv_val, compV_of _ g hg]
    show mp K (comp1 (B.A.act (-1)) (pt V (n := 1) d 0)) = _
    rw [gt_comp1_pt_right]
    rfl
  have hL2 : ev ![B.actK K (-1)] (B.hL K h w0) = ev ![mp K (g⁻¹).1, mp K ((Sm.act B w0 g)⁻¹).1] h := by
    rw [← ha, ev_hL K B h w0 (g⁻¹).1 hgi, ← map_inv (Sm.act B w0) g, Sm.act_val, compV_of _ _ hgi]
  have key : jo * (u3 p₁ g g⁻¹ (Sm.act B w0 g)).val = (u3 p₂ g⁻¹ (Sm.act B w0 g) (Sm.act B w0 g)⁻¹).val := by
    apply eq_of_toK_eq_of_injective K hi
    have hm : ∀ a b : PS V 1 d, FB.toK K (a * b) = FB.toK K a * FB.toK K b := fun a b => by
      unfold FB.toK
      exact map_mul _ _ _
    rw [hm, hj]
    unfold u3
    rw [evU_val, evU_val, e₁, e₂, canonicalGauge_first_partial_law_in_field K hh g g⁻¹ _ hg hgi hwg, canonicalGauge_second_partial_law_in_field K hh g⁻¹ _ _ hgi hwg hwgi,
      mul_inv_cancel, mul_inv_cancel, Sm.one_val, mp_zero K, ev_zero_zero_gp_eq_one_of_ev_zero_pt_pt_eq_one K hh _ (constantCoeff_baseChange_eq_zero K hwg),
      canonicalGauge_eval_zero_right K hh _ (constantCoeff_baseChange_eq_zero K hgi), hL2, hL1]
    have cA := c2 _ _ (constantCoeff_baseChange_eq_zero K hgi) (constantCoeff_baseChange_eq_zero K hwgi)
    have cB := c2 _ _ (constantCoeff_baseChange_eq_zero K hg) (constantCoeff_baseChange_eq_zero K hwg)
    have cQ := c2 _ _ (constantCoeff_baseChange_eq_zero K hgi) (constantCoeff_baseChange_eq_zero K hwg)
    rw [← gt_expS_add]
    · congr 1
      ring
    · simp [cA, cB]
    · simp [cB, cQ]
  unfold quadN
  rw [div_eq_mul_inv, Units.val_mul, ← key, _root_.mul_assoc, Units.mul_inv, _root_.mul_one]

end GlobalTheory.TransUnit.IotaLaw

namespace GlobalTheory.TransUnit

theorem evA_iota_eq_quadN : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB V d O) (K : Type) [Field K] [Algebra ℚ K] [Algebra V K] [IsFractionRing V K] (h : PS K 2 d) (w0 : O), B.IsCanonGauge K h → ∀ (p₁ p₂ : (PS V 3 d)ˣ), p₁.val = B.ph1 → p₂.val = B.ph2 → ∀ jo : PS V 1 d, IsIota B K h w0 jo → ∀ (n : ℕ) (x : Sm B n), evA ![x] jo = (quadN (u3 p₁) (u3 p₂) (Sm.act B w0) x).val := by
  intro V _ _ _ _ _ d O _ _ B K _ _ _ _ h w0 hh p₁ p₂ e₁ e₂ jo hj n x
  rw [IotaLaw.iota_gen K (IsFractionRing.injective V K) hh w0 p₁ p₂ e₁ e₂ jo hj, ← evU_val,
    ← quadN_map (Sm.sub ![x]) (evU ![x]) (fun y => (Sm.sub_act ![x] w0 y).symm) (fun a b c => unitSeriesValueThreePoints_substitution ![x] p₁ a b c)
      (fun a b c => unitSeriesValueThreePoints_substitution ![x] p₂ a b c) (Sm.gen B 0), Sm.sub_gen]
  rfl

end GlobalTheory.TransUnit
