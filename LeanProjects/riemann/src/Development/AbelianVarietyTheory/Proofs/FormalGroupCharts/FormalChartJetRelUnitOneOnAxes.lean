import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.AdditionLawSecondIdentity
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GaugeTrans

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing

namespace GlobalTheory.ChartCmp.Axes

variable {R : Type} [CommRing R]

theorem jEq_iff_order {σ : Type} (m : ℕ) (f g : MvPowerSeries σ R) :
    JEq m f g ↔ ((m + 1 : ℕ) : ℕ∞) ≤ MvPowerSeries.order (f - g) := by
  constructor
  · intro h
    refine MvPowerSeries.nat_le_order fun e he => ?_
    rw [map_sub, h e (by omega), sub_self]
  · intro h e he
    have : MvPowerSeries.coeff e (f - g) = 0 :=
      MvPowerSeries.coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_of_le he) h)
    rwa [map_sub, sub_eq_zero] at this

theorem jEq_mul_right {σ : Type} {m : ℕ} {f g : MvPowerSeries σ R} (u : MvPowerSeries σ R) (h : JEq m f g) :
    JEq m (f * u) (g * u) := by
  rw [jEq_iff_order] at h ⊢
  rw [← sub_mul]
  exact h.trans (le_self_add.trans MvPowerSeries.le_order_mul)

theorem jEq_ev {d n n' m : ℕ} (a : Fin n → Pt R n' d) (ha : ∀ j, GP (a j)) {f g : PS R n d} (h : JEq m f g) :
    JEq m (ev a f) (ev a g) := by
  classical
  intro e he
  unfold ev
  rw [MvPowerSeries.coeff_subst (gt_hasSubst a ha), MvPowerSeries.coeff_subst (gt_hasSubst a ha)]
  refine finsum_congr fun c => ?_
  by_cases hc : c.degree ≤ m
  · rw [h c hc]
  · have : MvPowerSeries.coeff e (c.prod fun s k => (a s.1 s.2) ^ k) = 0 := by
      apply MvPowerSeries.coeff_of_lt_order
      refine lt_of_lt_of_le ?_ (MvPowerSeries.le_order_prod _ _)
      have h1 : ((c.degree : ℕ) : ℕ∞) ≤ ∑ s ∈ c.support, MvPowerSeries.order ((a s.1 s.2) ^ c s) := by
        rw [Finsupp.degree_apply, Nat.cast_sum]
        refine Finset.sum_le_sum fun s _ => ?_
        exact MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero _ (ha s.1 s.2)
      refine lt_of_lt_of_le ?_ h1
      exact_mod_cast (by omega : e.degree < c.degree)
    rw [this, smul_zero, smul_zero]

theorem jEq_one_of_idem {σ : Type} {m : ℕ} {e : MvPowerSeries σ R} (hu : IsUnit (MvPowerSeries.constantCoeff e))
    (h : JEq m e (e * e)) : JEq m e 1 := by
  obtain ⟨u, rfl⟩ := MvPowerSeries.isUnit_iff_constantCoeff.2 hu
  have := jEq_mul_right (↑u⁻¹ : MvPowerSeries σ R) h
  rw [_root_.mul_assoc, Units.mul_inv, _root_.mul_one] at this
  exact fun e he => (this e he).symm

theorem vec3 {d m n : ℕ} (V : Fin m → Pt R n d) (a b c : Pt R m d) :
    (fun j => evP V (![a, b, c] j)) = ![evP V a, evP V b, evP V c] := by
  funext j; fin_cases j <;> rfl

theorem addOf_zero {d n : ℕ} (F : Fin d → PS R 2 d) (hF : ∀ i, MvPowerSeries.constantCoeff (F i) = 0) :
    addOf F (0 : Pt R n d) 0 = 0 := by
  funext i
  change MvPowerSeries.subst (fun p : Fin 2 × Fin d => (![(0 : Pt R n d), 0] p.1) p.2) (F i) = 0
  have e : (fun p : Fin 2 × Fin d => (![(0 : Pt R n d), 0] p.1) p.2) = 0 := by
    funext p
    obtain ⟨j, l⟩ := p
    fin_cases j <;> rfl
  rw [e]
  exact MvPowerSeries.subst_zero_of_constantCoeff_zero (hF i)

theorem ev_zero_zero_gp_eq_one_of_ev_zero_pt_pt_eq_one {d n : ℕ} (f : PS R 3 d) (hf : ev (n := 2) ![0, pt R d 0, pt R d 1] f = 1) (z : Pt R n d) (hz : GP z) :
    ev ![0, 0, z] f = 1 := by
  have hV : ∀ j, GP (![(0 : Pt R n d), z] j) := pair_points_zero_constant gp_zero₂ hz
  have := congrArg (ev ![0, z]) hf
  rw [gt_ev_ev' _ _ hV (triple_points_zero_constant gp_zero₂ (gp_pt 0) (gp_pt 1)), vec3, evP_zero _ hV, evP_pt _ hV,
    evP_pt _ hV, ev_one] at this
  exact this

theorem ev_gp_zero_zero_eq_one_of_ev_pt_pt_zero_eq_one {d n : ℕ} (f : PS R 3 d) (hf : ev (n := 2) ![pt R d 0, pt R d 1, 0] f = 1) (z : Pt R n d) (hz : GP z) :
    ev ![z, 0, 0] f = 1 := by
  have hV : ∀ j, GP (![z, (0 : Pt R n d)] j) := pair_points_zero_constant hz gp_zero₂
  have := congrArg (ev ![z, 0]) hf
  rw [gt_ev_ev' _ _ hV (triple_points_zero_constant (gp_pt 0) (gp_pt 1) gp_zero₂), vec3, evP_zero _ hV, evP_pt _ hV,
    evP_pt _ hV, ev_one] at this
  exact this

end GlobalTheory.ChartCmp.Axes

open GlobalTheory.ChartCmp.Axes in

theorem GlobalTheory.ChartCmp.jRel_axes : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (m : ℕ) (B B' : FB R d O) (φ φi : Pt R 1 d) (ε : PS R 2 d), JRel m B B' φ φi ε → MvPowerSeries.constantCoeff ε = 1 ∧ JEq m (ev (n := 1) ![0, pt R (n := 1) d 0] ε) 1 ∧ JEq m (ev (n := 1) ![pt R (n := 1) d 0, 0] ε) 1 := by
  intro R _ d O _ _ m B B' φ φi ε h
  have hφ : GP φ := h.inv.1
  have hp : ∀ {n : ℕ} (j : Fin n), GP (pt R (n := n) d j) := fun j => gp_pt j
  have hz : ∀ {n : ℕ}, GP (0 : Pt R n d) := gp_zero₂
  have hc : ∀ {n : ℕ} (j : Fin n), GP (comp1 φ (pt R (n := n) d j)) := fun j => gp_comp1 φ _ hφ (hp j)
  have h1 : JEq m (ev (n := 1) ![0, pt R (n := 1) d 0] ε) 1 := by
    have hV : ∀ j, GP (![(0 : Pt R 1 d), 0, pt R (n := 1) d 0] j) := triple_points_zero_constant hz hz (hp 0)
    have H := jEq_ev _ hV h.ph1
    rw [gt_ev_mul _ hV, gt_ev_mul _ hV, gt_ev_mul _ hV, ev_zero_zero_gp_eq_one_of_ev_zero_pt_pt_eq_one _ B'.cocycleLeft_zero_fst _ (hp 0), _root_.one_mul,
      gt_ev_ev' _ _ hV (pair_points_zero_constant (gp_addOf _ B'.G.const _ _ (hp 0) (hp 1)) (hp 2)),
      gt_ev_ev' _ _ hV (triple_points_zero_constant (hc 0) (hc 1) (hc 2)), gt_ev_ev' _ _ hV (pair_points_zero_constant (hp 0) (hp 2)),
      gt_ev_ev' _ _ hV (pair_points_zero_constant (hp 1) (hp 2)), vec3, eval_pair_points, eval_pair_points, eval_pair_points,
      evP_addOf _ hV _ _ _ (hp 0) (hp 1), evP_comp1 _ hV _ _ (hp 0), evP_comp1 _ hV _ _ (hp 1),
      evP_comp1 _ hV _ _ (hp 2), evP_pt _ hV, evP_pt _ hV, evP_pt _ hV] at H
    change JEq m (ev ![addOf B'.G.F 0 0, pt R (n := 1) d 0] ε)
      (ev ![comp1 φ 0, comp1 φ 0, comp1 φ (pt R (n := 1) d 0)] B.ph1 *
        (ev ![0, pt R (n := 1) d 0] ε * ev ![0, pt R (n := 1) d 0] ε)) at H
    rw [addOf_zero _ B'.G.const, gt_comp1_zero φ hφ, ev_zero_zero_gp_eq_one_of_ev_zero_pt_pt_eq_one _ B.cocycleLeft_zero_fst _ (hc 0), _root_.one_mul] at H
    refine jEq_one_of_idem ?_ H
    rw [gt_const_ev_eq _ (pair_points_zero_constant hz (hp 0))]
    exact h.unit
  have h2 : JEq m (ev (n := 1) ![pt R (n := 1) d 0, 0] ε) 1 := by
    have hV : ∀ j, GP (![pt R (n := 1) d 0, (0 : Pt R 1 d), 0] j) := triple_points_zero_constant (hp 0) hz hz
    have H := jEq_ev _ hV h.ph2
    rw [gt_ev_mul _ hV, gt_ev_mul _ hV, gt_ev_mul _ hV, ev_gp_zero_zero_eq_one_of_ev_pt_pt_zero_eq_one _ B'.cocycleRight_zero_thd _ (hp 0), _root_.one_mul,
      gt_ev_ev' _ _ hV (pair_points_zero_constant (hp 0) (gp_addOf _ B'.G.const _ _ (hp 1) (hp 2))),
      gt_ev_ev' _ _ hV (triple_points_zero_constant (hc 0) (hc 1) (hc 2)), gt_ev_ev' _ _ hV (pair_points_zero_constant (hp 0) (hp 1)),
      gt_ev_ev' _ _ hV (pair_points_zero_constant (hp 0) (hp 2)), vec3, eval_pair_points, eval_pair_points, eval_pair_points,
      evP_addOf _ hV _ _ _ (hp 1) (hp 2), evP_comp1 _ hV _ _ (hp 0), evP_comp1 _ hV _ _ (hp 1),
      evP_comp1 _ hV _ _ (hp 2), evP_pt _ hV, evP_pt _ hV, evP_pt _ hV] at H
    change JEq m (ev ![pt R (n := 1) d 0, addOf B'.G.F 0 0] ε)
      (ev ![comp1 φ (pt R (n := 1) d 0), comp1 φ 0, comp1 φ 0] B.ph2 *
        (ev ![pt R (n := 1) d 0, 0] ε * ev ![pt R (n := 1) d 0, 0] ε)) at H
    rw [addOf_zero _ B'.G.const, gt_comp1_zero φ hφ, ev_gp_zero_zero_eq_one_of_ev_pt_pt_zero_eq_one _ B.cocycleRight_zero_thd _ (hc 0), _root_.one_mul] at H
    refine jEq_one_of_idem ?_ H
    rw [gt_const_ev_eq _ (pair_points_zero_constant (hp 0) hz)]
    exact h.unit
  refine ⟨?_, h1, h2⟩
  have := h1 0 (by simp)
  rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
    gt_const_ev_eq _ (pair_points_zero_constant hz (hp 0)), map_one] at this
  exact this
