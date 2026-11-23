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

namespace GlobalTheory.TransUnit.ThetaLaw

section Exp
variable (K : Type) [CommRing K] [Algebra ℚ K] (n d : ℕ)

def noConst : AddSubgroup (PS K n d) where
  carrier := {g | MvPowerSeries.constantCoeff g = 0}
  zero_mem' := map_zero _
  add_mem' := fun {f g} hf hg => by
    change MvPowerSeries.constantCoeff (f + g) = 0
    rw [map_add, hf, hg, add_zero]
  neg_mem' := fun {f} hf => by
    change MvPowerSeries.constantCoeff (-f) = 0
    rw [map_neg, hf, neg_zero]

def expU : Multiplicative (noConst K n d) →* (PS K n d)ˣ :=
  MonoidHom.toHomUnits
    { toFun := fun g => FB.expS K (g.toAdd : PS K n d)
      map_one' := expS_zero K
      map_mul' := fun f g => gt_expS_add _ _ f.toAdd.2 g.toAdd.2 }

theorem expU_val (g : Multiplicative (noConst K n d)) : (expU K n d g).val = FB.expS K (g.toAdd : PS K n d) := rfl

end Exp

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V]
  {d : ℕ} {O : Type} [CommRing O] [StarRing O] (B : FB V d O) {n : ℕ}

theorem smallFormalGroupPoints_mul_coe_eq_formalAdd (x y : Sm B n) (hx : GP x.1) (hy : GP y.1) : (x * y).1 = addOf B.G.F x.1 y.1 := by
  have hc : ∀ j i, MvPowerSeries.constantCoeff ((![x, y] j).1 i) = 0 := by
    intro j i
    fin_cases j
    · exact hx i
    · exact hy i
  have hv : (fun j => (![x, y] j).1) = ![x.1, y.1] := by
    funext j
    fin_cases j <;> rfl
  rw [Sm.mul_val]
  funext i
  have e := evA_eq_ev ![x, y] hc (B.G.F i)
  rw [smallPointsSubstitutionAlgHom_two_points, hv] at e
  exact e

theorem smallPointsRingAction_coe_eq_comp (o : O) (x : Sm B n) (hx : GP x.1) : (Sm.act B o x).1 = comp1 (B.A.act o) x.1 := by
  have hc : ∀ j i, MvPowerSeries.constantCoeff ((![x] j).1 i) = 0 := by
    intro j i
    fin_cases j
    exact hx i
  have hv : (fun j => (![x] j).1) = ![x.1] := by
    funext j
    fin_cases j
    rfl
  rw [Sm.act_val]
  funext i
  have e := evA_eq_ev ![x] hc (B.A.act o i)
  rw [smallPointsSubstitutionAlgHom_single_point, hv] at e
  exact e

theorem smallPointsSubstitution_three_eq_eval (x y z : Sm B n) (hx : GP x.1) (hy : GP y.1) (hz : GP z.1) (f : PS V 3 d) :
    evA ![x, y, z] f = ev ![x.1, y.1, z.1] f := by
  have hc : ∀ j i, MvPowerSeries.constantCoeff ((![x, y, z] j).1 i) = 0 := by
    intro j i
    fin_cases j
    · exact hx i
    · exact hy i
    · exact hz i
  have hv : (fun j => (![x, y, z] j).1) = ![x.1, y.1, z.1] := by
    funext j
    fin_cases j <;> rfl
  rw [evA_eq_ev _ hc, hv]

theorem constantCoeff_act_eq_zero (o : O) (x : Sm B n) (hx : GP x.1) : GP (Sm.act B o x).1 := by
  rw [smallPointsRingAction_coe_eq_comp B o x hx]
  exact gp_comp1 _ _ (fun i => B.A.const o i) hx

variable (n) in

def zeroPts : Subgroup (Sm B n) where
  carrier := {x | GP x.1}
  one_mem' := gp_zero₂
  mul_mem' := fun {x y} hx hy => by
    change GP (x * y).1
    rw [smallFormalGroupPoints_mul_coe_eq_formalAdd B x y hx hy]
    exact gp_addOf _ B.G.const _ _ hx hy
  inv_mem' := fun {x} hx => constantCoeff_act_eq_zero B (-1) x hx

def act0 (o : O) : zeroPts B n →* zeroPts B n :=
  ((Sm.act B o).comp (zeroPts B n).subtype).codRestrict _ fun x => constantCoeff_act_eq_zero B o x.1 x.2

variable (K : Type) [CommRing K] [Algebra ℚ K] [Algebra V K] {h : PS K 2 d}

def negH (hh : B.IsCanonGauge K h) (a b : zeroPts B n) : Multiplicative (noConst K n d) :=
  Multiplicative.ofAdd (-⟨ev ![mp K a.1.1, mp K b.1.1] h,
    gt_const_ev _ (pair_points_zero_constant (constantCoeff_baseChange_eq_zero K a.2) (constantCoeff_baseChange_eq_zero K b.2)) _ (cc_gauge K B hh)⟩)

theorem negH_val (hh : B.IsCanonGauge K h) (a b : zeroPts B n) :
    ((negH B K hh a b).toAdd : PS K n d) = -ev ![mp K a.1.1, mp K b.1.1] h := rfl

private theorem mp_mul_eq_addOf (x y : zeroPts B n) :
    mp K (x * y).1.1 = addOf (B.FK K) (mp K x.1.1) (mp K y.1.1) := by
  rw [show (x * y).1.1 = addOf B.G.F x.1.1 y.1.1 from smallFormalGroupPoints_mul_coe_eq_formalAdd B x.1 y.1 x.2 y.2]
  rw [mp_addOf K B.G x.1.1 y.1.1 x.2 y.2]
  rfl

theorem canonicalGauge_first_partial_law_eq (hh : B.IsCanonGauge K h) (a b c : zeroPts B n) :
    FB.toK K (evA ![a.1, b.1, c.1] B.ph1) =
      (expU K n d (negH B K hh (a * b) c / (negH B K hh a c * negH B K hh b c))).val := by
  have hc := cc_gauge K B hh
  have ha : GP a.1.1 := a.2
  have hb : GP b.1.1 := b.2
  have hc' : GP c.1.1 := c.2
  have g0 := gp_pt (k := K) (n := 3) (d := d) 0
  have g1 := gp_pt (k := K) (n := 3) (d := d) 1
  have g2 := gp_pt (k := K) (n := 3) (d := d) 2
  have gs := gp_addOf (B.FK K) (cc_FK K B) _ _ g0 g1
  have hV : ∀ j, GP (![mp K a.1.1, mp K b.1.1, mp K c.1.1] j) := triple_points_zero_constant (constantCoeff_baseChange_eq_zero K ha) (constantCoeff_baseChange_eq_zero K hb) (constantCoeff_baseChange_eq_zero K hc')
  have hv : (fun j => mp K (![a.1.1, b.1.1, c.1.1] j)) = ![mp K a.1.1, mp K b.1.1, mp K c.1.1] := by
    funext j
    fin_cases j <;> rfl
  have e1 : ∀ p q : Pt K 3 d, GP p → GP q → ev ![mp K a.1.1, mp K b.1.1, mp K c.1.1] (ev ![p, q] h) =
      ev ![evP ![mp K a.1.1, mp K b.1.1, mp K c.1.1] p, evP ![mp K a.1.1, mp K b.1.1, mp K c.1.1] q] h := by
    intro p q hp hq
    rw [gt_ev_ev' _ _ hV (pair_points_zero_constant hp hq), eval_pair_points]
  rw [smallPointsSubstitution_three_eq_eval B a.1 b.1 c.1 ha hb hc', toK_ev K _ (triple_points_zero_constant ha hb hc'), hv, hh.ph1, gt_ev_expS _ hV, expU_val]
  · congr 1
    rw [gt_ev_sub _ hV, gt_ev_add _ hV, e1 _ _ g0 g2, e1 _ _ g1 g2, e1 _ _ gs g2, evP_addOf _ hV _ _ _ g0 g1,
      evP_pt _ hV, evP_pt _ hV, evP_pt _ hV]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
      ← mp_mul_eq_addOf B K a b, toAdd_div, toAdd_mul, AddSubgroup.coe_sub, AddSubgroup.coe_add, negH_val B K hh]
    abel
  · rw [map_sub, map_add, gt_const_ev _ (pair_points_zero_constant g0 g2) _ hc, gt_const_ev _ (pair_points_zero_constant g1 g2) _ hc,
      gt_const_ev _ (pair_points_zero_constant gs g2) _ hc]
    simp

theorem ph2_eq_subst_exp (hh : B.IsCanonGauge K h) (a b c : zeroPts B n) :
    FB.toK K (evA ![a.1, b.1, c.1] B.ph2) =
      (expU K n d (negH B K hh a (b * c) / (negH B K hh a b * negH B K hh a c))).val := by
  have hc := cc_gauge K B hh
  have ha : GP a.1.1 := a.2
  have hb : GP b.1.1 := b.2
  have hc' : GP c.1.1 := c.2
  have g0 := gp_pt (k := K) (n := 3) (d := d) 0
  have g1 := gp_pt (k := K) (n := 3) (d := d) 1
  have g2 := gp_pt (k := K) (n := 3) (d := d) 2
  have gs := gp_addOf (B.FK K) (cc_FK K B) _ _ g1 g2
  have hV : ∀ j, GP (![mp K a.1.1, mp K b.1.1, mp K c.1.1] j) := triple_points_zero_constant (constantCoeff_baseChange_eq_zero K ha) (constantCoeff_baseChange_eq_zero K hb) (constantCoeff_baseChange_eq_zero K hc')
  have hv : (fun j => mp K (![a.1.1, b.1.1, c.1.1] j)) = ![mp K a.1.1, mp K b.1.1, mp K c.1.1] := by
    funext j
    fin_cases j <;> rfl
  have e1 : ∀ p q : Pt K 3 d, GP p → GP q → ev ![mp K a.1.1, mp K b.1.1, mp K c.1.1] (ev ![p, q] h) =
      ev ![evP ![mp K a.1.1, mp K b.1.1, mp K c.1.1] p, evP ![mp K a.1.1, mp K b.1.1, mp K c.1.1] q] h := by
    intro p q hp hq
    rw [gt_ev_ev' _ _ hV (pair_points_zero_constant hp hq), eval_pair_points]
  rw [smallPointsSubstitution_three_eq_eval B a.1 b.1 c.1 ha hb hc', toK_ev K _ (triple_points_zero_constant ha hb hc'), hv, hh.ph2, gt_ev_expS _ hV, expU_val]
  · congr 1
    rw [gt_ev_sub _ hV, gt_ev_add _ hV, e1 _ _ g0 g1, e1 _ _ g0 g2, e1 _ _ g0 gs, evP_addOf _ hV _ _ _ g1 g2,
      evP_pt _ hV, evP_pt _ hV, evP_pt _ hV]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
      ← mp_mul_eq_addOf B K b c, toAdd_div, toAdd_mul, AddSubgroup.coe_sub, AddSubgroup.coe_add, negH_val B K hh]
    abel
  · rw [map_sub, map_add, gt_const_ev _ (pair_points_zero_constant g0 g1) _ hc, gt_const_ev _ (pair_points_zero_constant g0 g2) _ hc,
      gt_const_ev _ (pair_points_zero_constant g0 gs) _ hc]
    simp

theorem negH_act (hh : B.IsCanonGauge K h) (w : O) (a : zeroPts B n) :
    ((negH B K hh a (act0 B w a)).toAdd : PS K n d) = -ev ![mp K a.1.1] (B.hL K h w) := by
  rw [negH_val, ev_hL (K := K) (B := B) h w a.1.1 a.2]
  rw [show (act0 B w a).1.1 = comp1 (B.A.act w) a.1.1 from smallPointsRingAction_coe_eq_comp B w a.1 a.2]

theorem quadQ_eq (hh : B.IsCanonGauge K h) (w : O) (p₁ p₂ : (PS V 3 d)ˣ) (h₁ : p₁.val = B.ph1) (h₂ : p₂.val = B.ph2)
    (a b c : zeroPts B n) :
    FB.toK K (quadQ (u3 p₁) (u3 p₂) (Sm.act B w) a.1 b.1 c.1).val =
      (expU K n d (c3 (fun x => negH B K hh x (act0 B w x)) a b c)).val := by
  have s1 : quadQ (u3 p₁) (u3 p₂) (Sm.act B w) a.1 b.1 c.1 =
      quadQ (fun x y z : zeroPts B n => u3 p₁ x.1 y.1 z.1) (fun x y z : zeroPts B n => u3 p₂ x.1 y.1 z.1)
        (act0 B w) a b c :=
    quadQ_map (zeroPts B n).subtype (MonoidHom.id _) (p₁ := fun x y z : zeroPts B n => u3 p₁ x.1 y.1 z.1)
      (p₂ := fun x y z : zeroPts B n => u3 p₂ x.1 y.1 z.1) (p₁' := u3 p₁) (p₂' := u3 p₂) (w := act0 B w)
      (w' := Sm.act B w) (fun _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl) a b c
  let g : (PS V n d)ˣ →* (PS K n d)ˣ := Units.map ((MvPowerSeries.map (algebraMap V K) : PS V n d →+* PS K n d) : PS V n d →* PS K n d)
  have s2 : quadQ (fun x y z : zeroPts B n => g (u3 p₁ x.1 y.1 z.1)) (fun x y z : zeroPts B n => g (u3 p₂ x.1 y.1 z.1))
        (act0 B w) a b c =
      g (quadQ (fun x y z : zeroPts B n => u3 p₁ x.1 y.1 z.1) (fun x y z : zeroPts B n => u3 p₂ x.1 y.1 z.1)
        (act0 B w) a b c) :=
    quadQ_map (MonoidHom.id _) g (p₁ := fun x y z : zeroPts B n => u3 p₁ x.1 y.1 z.1)
      (p₂ := fun x y z : zeroPts B n => u3 p₂ x.1 y.1 z.1)
      (p₁' := fun x y z : zeroPts B n => g (u3 p₁ x.1 y.1 z.1)) (p₂' := fun x y z : zeroPts B n => g (u3 p₂ x.1 y.1 z.1))
      (w := act0 B w) (w' := act0 B w) (fun _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl) a b c
  have s3 : quadQ (fun x y z : zeroPts B n => g (u3 p₁ x.1 y.1 z.1)) (fun x y z : zeroPts B n => g (u3 p₂ x.1 y.1 z.1))
        (act0 B w) a b c =
      quadQ (fun _ _ _ => (1 : (PS K n d)ˣ)) (fun _ _ _ => 1) (act0 B w) a b c *
        c3 (fun x => expU K n d (negH B K hh x (act0 B w x))) a b c := by
    refine quadQ_of_diff (e := fun x y => expU K n d (negH B K hh x y)) (act0 B w) (fun x y z => ?_) (fun x y z => ?_) a b c
    · show g (u3 p₁ x.1 y.1 z.1) = 1 * (expU K n d (negH B K hh (x * y) z) /
        (expU K n d (negH B K hh x z) * expU K n d (negH B K hh y z)))
      rw [_root_.one_mul, ← map_mul (expU K n d), ← map_div (expU K n d)]
      apply Units.ext
      rw [← canonicalGauge_first_partial_law_eq B K hh x y z]
      show FB.toK K (u3 p₁ x.1 y.1 z.1).val = _
      rw [u3, evU_val, h₁]
    · show g (u3 p₂ x.1 y.1 z.1) = 1 * (expU K n d (negH B K hh x (y * z)) /
        (expU K n d (negH B K hh x y) * expU K n d (negH B K hh x z)))
      rw [_root_.one_mul, ← map_mul (expU K n d), ← map_div (expU K n d)]
      apply Units.ext
      rw [← ph2_eq_subst_exp B K hh x y z]
      show FB.toK K (u3 p₂ x.1 y.1 z.1).val = _
      rw [u3, evU_val, h₂]
  rw [s1]
  show (g (quadQ (fun x y z : zeroPts B n => u3 p₁ x.1 y.1 z.1) (fun x y z : zeroPts B n => u3 p₂ x.1 y.1 z.1)
    (act0 B w) a b c)).val = _
  rw [← s2, s3, quadQ_one, _root_.one_mul]
  exact congrArg Units.val (map_lineCoeffCubic (MonoidHom.id _) (expU K n d) (q := fun x => negH B K hh x (act0 B w x))
    (q' := fun x => expU K n d (negH B K hh x (act0 B w x))) (fun _ => rfl) a b c)

theorem universal (hi : Function.Injective (algebraMap V K)) (hh : B.IsCanonGauge K h) (w : O) (p₁ p₂ : (PS V 3 d)ˣ)
    (h₁ : p₁.val = B.ph1) (h₂ : p₂.val = B.ph2) (Θ : PS V 3 d) (hΘ : IsTheta B K h w Θ) :
    Θ * (quadQ (u3 p₁) (u3 p₂) (Sm.act B w) (Sm.gen B 0) (Sm.gen B 1) (Sm.gen B 2)).val = 1 := by
  have hinj : Function.Injective (FB.toK K : PS V 3 d → PS K 3 d) := by
    intro f g hfg
    ext m
    have e := congrArg (MvPowerSeries.coeff m) hfg
    simp only [FB.toK, MvPowerSeries.coeff_map] at e
    exact hi e
  let a0 : zeroPts B 3 := ⟨Sm.gen B 0, gp_pt (k := V) (d := d) 0⟩
  let a1 : zeroPts B 3 := ⟨Sm.gen B 1, gp_pt (k := V) (d := d) 1⟩
  let a2 : zeroPts B 3 := ⟨Sm.gen B 2, gp_pt (k := V) (d := d) 2⟩
  have hq : FB.toK K (quadQ (u3 p₁) (u3 p₂) (Sm.act B w) (Sm.gen B 0) (Sm.gen B 1) (Sm.gen B 2)).val =
      (expU K 3 d (c3 (fun x => negH B K hh x (act0 B w x)) a0 a1 a2)).val :=
    quadQ_eq B K hh w p₁ p₂ h₁ h₂ a0 a1 a2
  have m0 : mp K a0.1.1 = pt K d 0 := mp_pt (V := V) (d := d) K 0
  have m1 : mp K a1.1.1 = pt K d 1 := mp_pt (V := V) (d := d) K 1
  have m2 : mp K a2.1.1 = pt K d 2 := mp_pt (V := V) (d := d) K 2
  have hT : FB.toK K Θ = (expU K 3 d (c3 (fun x => negH B K hh x (act0 B w x)) a0 a1 a2)⁻¹).val := by
    rw [expU_val]
    dsimp only [IsTheta] at hΘ
    rw [hΘ]
    congr 1
    simp only [c3, toAdd_inv, toAdd_div, toAdd_mul, AddSubgroup.coe_neg, AddSubgroup.coe_sub, AddSubgroup.coe_add,
      negH_act B K hh w, mp_mul_eq_addOf B K, m0, m1, m2]
    abel
  have tm : ∀ f g : PS V 3 d, FB.toK K (f * g) = FB.toK K f * FB.toK K g := fun f g =>
    map_mul (MvPowerSeries.map (algebraMap V K)) f g
  have t1 : FB.toK K (1 : PS V 3 d) = 1 := map_one (MvPowerSeries.map (algebraMap V K))
  apply hinj
  rw [tm, t1, hT, hq, ← Units.val_mul, ← map_mul (expU K 3 d), _root_.inv_mul_cancel, map_one, Units.val_one]

end GlobalTheory.TransUnit.ThetaLaw

namespace GlobalTheory.TransUnit

theorem evA_theta_mul_quadQ :
    ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB V d O) (K : Type) [Field K] [Algebra ℚ K] [Algebra V K] [IsFractionRing V K] (h : PS K 2 d) (w0 : O), B.IsCanonGauge K h → ∀ (p₁ p₂ : (PS V 3 d)ˣ), p₁.val = B.ph1 → p₂.val = B.ph2 → ∀ Θ : PS V 3 d, IsTheta B K h w0 Θ → ∀ (n : ℕ) (x y z : Sm B n), evA ![x, y, z] Θ * (quadQ (u3 p₁) (u3 p₂) (Sm.act B w0) x y z).val = 1 := by
  intro V _ _ _ _ _ d O _ _ B K _ _ _ _ h w0 hh p₁ p₂ h₁ h₂ Θ hΘ n x y z
  have hu := ThetaLaw.universal B K (IsFractionRing.injective V K) hh w0 p₁ p₂ h₁ h₂ Θ hΘ
  have hm : quadQ (u3 p₁) (u3 p₂) (Sm.act B w0) x y z =
      evU ![x, y, z] (quadQ (u3 p₁) (u3 p₂) (Sm.act B w0) (Sm.gen B 0) (Sm.gen B 1) (Sm.gen B 2)) := by
    have e := quadQ_map (Sm.sub ![x, y, z]) (evU ![x, y, z]) (p₁ := u3 p₁) (p₂ := u3 p₂) (p₁' := u3 p₁)
      (p₂' := u3 p₂) (w := Sm.act B w0) (w' := Sm.act B w0) (fun a => (Sm.sub_act ![x, y, z] w0 a).symm)
      (fun a b c => unitSeriesValueThreePoints_substitution ![x, y, z] p₁ a b c) (fun a b c => unitSeriesValueThreePoints_substitution ![x, y, z] p₂ a b c)
      (Sm.gen B 0) (Sm.gen B 1) (Sm.gen B 2)
    rw [Sm.sub_gen, Sm.sub_gen, Sm.sub_gen] at e
    exact e
  rw [hm, evU_val, ← map_mul (evA ![x, y, z]), hu, map_one]

end GlobalTheory.TransUnit
