import Mathlib
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.MvPowerSeriesSubstConstTermsLocalAlgHomSpec
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GaugeTrans

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing

namespace GlobalTheory.PlaceInt.Kappa

section Basic
variable {V : Type} [CommRing V] {d : ℕ} (K : Type) [Field K] [Algebra ℚ K] [Algebra V K]

theorem expS_zero' {n : ℕ} : FB.expS K (0 : PS K n d) = 1 := by
  unfold FB.expS
  rw [PowerSeries.subst_zero_eq_C_constantCoeff]
  simp

theorem cc_expS {n : ℕ} (g : PS K n d) (hg : MvPowerSeries.constantCoeff g = 0) :
    MvPowerSeries.constantCoeff (FB.expS K g) = 1 := by
  have h0 : ∀ j : Fin n, GP ((fun _ => 0 : Fin n → Pt K n d) j) := fun _ => gp_zero₂
  rw [← gt_const_ev_eq _ h0, gt_ev_expS _ h0 g hg]
  have : ev (fun _ => 0 : Fin n → Pt K n d) g = 0 := MvPowerSeries.subst_zero_of_constantCoeff_zero hg
  rw [this, expS_zero', map_one]

theorem cc_eq_one (hi : Function.Injective (algebraMap V K)) {n : ℕ} (g : PS K n d)
    (hg : MvPowerSeries.constantCoeff g = 0) (u : PS V n d) (hu : FB.toK K u = FB.expS K g) :
    MvPowerSeries.constantCoeff u = 1 := by
  apply hi
  have := congrArg MvPowerSeries.constantCoeff hu
  rw [cc_expS K g hg, MvPowerSeries.constantCoeff_map] at this
  rw [this, map_one]

def intLog (hi : Function.Injective (algebraMap V K)) (n d : ℕ) : AddSubgroup (PS K n d) where
  carrier := {g | MvPowerSeries.constantCoeff g = 0 ∧ ∃ u : PS V n d, FB.toK K u = FB.expS K g}
  zero_mem' := ⟨map_zero _, 1, by rw [expS_zero']; exact map_one _⟩
  add_mem' := by
    rintro f g ⟨hf, u, hu⟩ ⟨hg, v, hv⟩
    refine ⟨by rw [map_add, hf, hg, add_zero], u * v, ?_⟩
    rw [gt_expS_add f g hf hg, ← hu, ← hv]
    exact map_mul _ _ _
  neg_mem' := by
    rintro g ⟨hg, u, hu⟩
    have hn : MvPowerSeries.constantCoeff (-g) = 0 := by rw [map_neg, hg, neg_zero]
    have hunit : IsUnit u := by
      rw [MvPowerSeries.isUnit_iff_constantCoeff, cc_eq_one K hi g hg u hu]
      exact isUnit_one
    obtain ⟨v, hv⟩ := hunit.exists_left_inv
    refine ⟨hn, v, ?_⟩
    have e1 : FB.expS K g * FB.expS K (-g) = 1 := by
      rw [← gt_expS_add g (-g) hg hn, add_neg_cancel, expS_zero']
    have e2 : FB.toK K v * FB.toK K u = 1 := by
      rw [← map_mul, hv, map_one]
    calc FB.toK K v = FB.toK K v * (FB.expS K g * FB.expS K (-g)) := by rw [e1, _root_.mul_one]
      _ = FB.expS K (-g) := by rw [← hu, ← _root_.mul_assoc, e2, _root_.one_mul]

def mp {n : ℕ} (x : Pt V n d) : Pt K n d := fun i => FB.toK K (x i)

theorem constantCoeff_baseChange_eq_zero {n : ℕ} {x : Pt V n d} (hx : GP x) : GP (mp K x) := fun i => by
  simp [mp, MvPowerSeries.constantCoeff_map, hx i]

theorem toK_ev {m n : ℕ} (a : Fin m → Pt V n d) (ha : ∀ j, GP (a j)) (f : PS V m d) :
    FB.toK K (ev a f) = ev (fun j => mp K (a j)) (FB.toK K f) := by
  unfold ev
  rw [FB.toK, MvPowerSeries.map_subst (gt_hasSubst a ha)]
  rfl

theorem mp_pt {n : ℕ} (j : Fin n) : mp K (pt V d j) = pt K d j := by
  funext i; simp [mp, pt]

theorem mp_zero {n : ℕ} : mp K (0 : Pt V n d) = 0 := by
  funext i; simp [mp]

theorem mp_comp1 {n : ℕ} (φ : Pt V 1 d) {x : Pt V n d} (hx : GP x) :
    mp K (comp1 φ x) = comp1 (mp K φ) (mp K x) := by
  funext i
  change FB.toK K (ev ![x] (φ i)) = ev ![mp K x] (FB.toK K (φ i))
  rw [toK_ev K _ (single_point_zero_constant hx)]
  congr 1
  funext j; fin_cases j; rfl

theorem mp_addOf {n : ℕ} (F : Fin d → PS V 2 d) {x y : Pt V n d} (hx : GP x) (hy : GP y) :
    mp K (addOf F x y) = addOf (fun i => FB.toK K (F i)) (mp K x) (mp K y) := by
  funext i
  change FB.toK K (ev ![x, y] (F i)) = ev ![mp K x, mp K y] (FB.toK K (F i))
  rw [toK_ev K _ (pair_points_zero_constant hx hy)]
  congr 1
  funext j; fin_cases j <;> rfl

theorem ev_mem (hi : Function.Injective (algebraMap V K)) {m n : ℕ} (a : Fin m → Pt V n d) (ha : ∀ j, GP (a j))
    (g : PS K m d) (hg : MvPowerSeries.constantCoeff g = 0) (u : PS V m d) (hu : FB.toK K u = FB.expS K g) :
    ev (fun j => mp K (a j)) g ∈ intLog K hi n d := by
  have ha' : ∀ j, GP (mp K (a j)) := fun j => constantCoeff_baseChange_eq_zero K (ha j)
  exact ⟨gt_const_ev _ ha' g hg, ev a u, by rw [toK_ev K a ha, hu, gt_ev_expS _ ha' g hg]⟩

theorem germEv_germEv_two_points {m n : ℕ} (A : Fin m → Pt K n d) (hA : ∀ j, GP (A j)) {p q : Pt K m d} (hp : GP p) (hq : GP q)
    (f : PS K 2 d) : ev A (ev ![p, q] f) = ev ![evP A p, evP A q] f := by
  rw [gt_ev_ev' A _ hA (pair_points_zero_constant hp hq), eval_pair_points]

end Basic

section Gauge
variable {V : Type} [CommRing V] {d : ℕ} {O : Type} [CommRing O] [StarRing O] (B : FB V d O)
  (K : Type) [Field K] [Algebra ℚ K] [Algebra V K] (hi : Function.Injective (algebraMap V K)) (h : PS K 2 d)

def hq {n : ℕ} (x z : Pt V n d) : PS K n d ⧸ intLog K hi n d :=
  QuotientAddGroup.mk' _ (ev ![mp K x, mp K z] h)

theorem GP_FK : ∀ i, MvPowerSeries.constantCoeff (B.FK K i) = 0 := fun i => by
  simp [FB.FK, FGLaw.mapF, MvPowerSeries.constantCoeff_map, B.G.const i]

theorem constantCoeff_act_eq_zero (a : O) : GP (B.A.act a) := B.A.const a

theorem constantCoeff_actK_eq_zero (a : O) : GP (B.actK K a) := constantCoeff_baseChange_eq_zero K (constantCoeff_act_eq_zero B a)

variable {B K h}

theorem cc_h (hh : B.IsCanonGauge K h) : MvPowerSeries.constantCoeff h = 0 := by
  have := congrArg MvPowerSeries.constantCoeff hh.ax0
  rwa [gt_const_ev_eq _ (pair_points_zero_constant gp_zero₂ (gp_pt 0)), map_zero] at this

theorem hq_zero_left (hh : B.IsCanonGauge K h) {n : ℕ} {z : Pt V n d} (hz : GP z) : hq K hi h 0 z = 0 := by
  have hz' := single_point_zero_constant (constantCoeff_baseChange_eq_zero K hz)
  have := congrArg (ev ![mp K z]) hh.ax0
  rw [germEv_germEv_two_points K _ hz' gp_zero₂ (gp_pt 0), evP_zero _ hz', evP_pt _ hz', gt_ev_zero _ hz'] at this
  rw [hq, mp_zero]
  erw [this]
  exact map_zero _

theorem hq_zero_right (hh : B.IsCanonGauge K h) {n : ℕ} {z : Pt V n d} (hz : GP z) : hq K hi h z 0 = 0 := by
  have hz' := single_point_zero_constant (constantCoeff_baseChange_eq_zero K hz)
  have := congrArg (ev ![mp K z]) hh.ax1
  rw [germEv_germEv_two_points K _ hz' (gp_pt 0) gp_zero₂, evP_zero _ hz', evP_pt _ hz', gt_ev_zero _ hz'] at this
  rw [hq, mp_zero]
  erw [this]
  exact map_zero _

theorem hq_add_left (hh : B.IsCanonGauge K h) {n : ℕ} {x y z : Pt V n d} (hx : GP x) (hy : GP y) (hz : GP z) :
    hq K hi h (addOf B.G.F x y) z = hq K hi h x z + hq K hi h y z := by
  have h0 := cc_h hh
  have p0 : GP (pt K (n := 3) d 0) := gp_pt 0
  have p1 : GP (pt K (n := 3) d 1) := gp_pt 1
  have p2 : GP (pt K (n := 3) d 2) := gp_pt 2
  have pa := gp_addOf _ (GP_FK B K) _ _ p0 p1
  have hA : ∀ j, GP ((fun j => mp K (![x, y, z] j)) j) := fun j => constantCoeff_baseChange_eq_zero K (triple_points_zero_constant hx hy hz j)
  have m := ev_mem K hi ![x, y, z] (triple_points_zero_constant hx hy hz) _ (by
    rw [map_sub, map_add, gt_const_ev _ (pair_points_zero_constant p0 p2) _ h0, gt_const_ev _ (pair_points_zero_constant p1 p2) _ h0,
      gt_const_ev _ (pair_points_zero_constant pa p2) _ h0]; simp) _ hh.ph1
  rw [gt_ev_sub _ hA, gt_ev_add _ hA, germEv_germEv_two_points K _ hA p0 p2, germEv_germEv_two_points K _ hA p1 p2, germEv_germEv_two_points K _ hA pa p2,
    evP_addOf _ hA _ _ _ p0 p1, evP_pt _ hA, evP_pt _ hA, evP_pt _ hA] at m
  unfold hq
  rw [← map_add, mp_addOf K _ hx hy, eq_comm, ← sub_eq_zero, ← map_sub, QuotientAddGroup.mk'_apply,
    QuotientAddGroup.eq_zero_iff]
  exact m

theorem hq_add_right (hh : B.IsCanonGauge K h) {n : ℕ} {x y z : Pt V n d} (hx : GP x) (hy : GP y) (hz : GP z) :
    hq K hi h x (addOf B.G.F y z) = hq K hi h x y + hq K hi h x z := by
  have h0 := cc_h hh
  have p0 : GP (pt K (n := 3) d 0) := gp_pt 0
  have p1 : GP (pt K (n := 3) d 1) := gp_pt 1
  have p2 : GP (pt K (n := 3) d 2) := gp_pt 2
  have pa := gp_addOf _ (GP_FK B K) _ _ p1 p2
  have hA : ∀ j, GP ((fun j => mp K (![x, y, z] j)) j) := fun j => constantCoeff_baseChange_eq_zero K (triple_points_zero_constant hx hy hz j)
  have m := ev_mem K hi ![x, y, z] (triple_points_zero_constant hx hy hz) _ (by
    rw [map_sub, map_add, gt_const_ev _ (pair_points_zero_constant p0 p1) _ h0, gt_const_ev _ (pair_points_zero_constant p0 p2) _ h0,
      gt_const_ev _ (pair_points_zero_constant p0 pa) _ h0]; simp) _ hh.ph2
  rw [gt_ev_sub _ hA, gt_ev_add _ hA, germEv_germEv_two_points K _ hA p0 p1, germEv_germEv_two_points K _ hA p0 p2, germEv_germEv_two_points K _ hA p0 pa,
    evP_addOf _ hA _ _ _ p1 p2, evP_pt _ hA, evP_pt _ hA, evP_pt _ hA] at m
  unfold hq
  rw [← map_add, mp_addOf K _ hy hz, eq_comm, ← sub_eq_zero, ← map_sub, QuotientAddGroup.mk'_apply,
    QuotientAddGroup.eq_zero_iff]
  exact m

theorem hq_act (hh : B.IsCanonGauge K h) (a : O) {n : ℕ} {x z : Pt V n d} (hx : GP x) (hz : GP z) :
    hq K hi h (comp1 (B.A.act a) x) z = hq K hi h x (comp1 (B.A.act (star a)) z) := by
  have h0 := cc_h hh
  have p0 : GP (pt K (n := 2) d 0) := gp_pt 0
  have p1 : GP (pt K (n := 2) d 1) := gp_pt 1
  have pa := gp_comp1 _ _ (constantCoeff_actK_eq_zero B K a) p0
  have pb := gp_comp1 _ _ (constantCoeff_actK_eq_zero B K (star a)) p1
  have hA : ∀ j, GP ((fun j => mp K (![x, z] j)) j) := fun j => constantCoeff_baseChange_eq_zero K (pair_points_zero_constant hx hz j)
  have m := ev_mem K hi ![x, z] (pair_points_zero_constant hx hz) _ (by
    rw [map_sub, gt_const_ev _ (pair_points_zero_constant pa p1) _ h0, gt_const_ev _ (pair_points_zero_constant p0 pb) _ h0]; simp) _ (hh.ad a)
  rw [gt_ev_sub _ hA, germEv_germEv_two_points K _ hA pa p1, germEv_germEv_two_points K _ hA p0 pb,
    evP_comp1 _ hA _ _ p0, evP_comp1 _ hA _ _ p1, evP_pt _ hA, evP_pt _ hA] at m
  unfold hq
  rw [mp_comp1 K _ hx, mp_comp1 K _ hz, ← sub_eq_zero, ← map_sub, QuotientAddGroup.mk'_apply,
    QuotientAddGroup.eq_zero_iff]
  exact m

variable (B)

theorem act_addOf (a : O) {n : ℕ} {x y : Pt V n d} (hx : GP x) (hy : GP y) :
    comp1 (B.A.act a) (addOf B.G.F x y) = addOf B.G.F (comp1 (B.A.act a) x) (comp1 (B.A.act a) y) := by
  have p0 : GP (pt V (n := 2) d 0) := gp_pt 0
  have p1 : GP (pt V (n := 2) d 1) := gp_pt 1
  have hA := pair_points_zero_constant hx hy
  have := congrArg (evP ![x, y]) (B.A.hom a)
  rw [evP_comp1 _ hA _ _ (gp_addOf _ B.G.const _ _ p0 p1), evP_addOf _ hA _ _ _ p0 p1,
    evP_addOf _ hA _ _ _ (gp_comp1 _ _ (constantCoeff_act_eq_zero B a) p0) (gp_comp1 _ _ (constantCoeff_act_eq_zero B a) p1),
    evP_comp1 _ hA _ _ p0, evP_comp1 _ hA _ _ p1, evP_pt _ hA, evP_pt _ hA] at this
  exact this

theorem add_act (a b : O) {n : ℕ} {x : Pt V n d} (hx : GP x) :
    comp1 (B.A.act (a + b)) x = addOf B.G.F (comp1 (B.A.act a) x) (comp1 (B.A.act b) x) := by
  rw [B.A.add_act]
  exact evP_addOf ![x] (single_point_zero_constant hx) _ _ _ (constantCoeff_act_eq_zero B a) (constantCoeff_act_eq_zero B b)

theorem mul_act (a b : O) {n : ℕ} {x : Pt V n d} (hx : GP x) :
    comp1 (B.A.act (a * b)) x = comp1 (B.A.act a) (comp1 (B.A.act b) x) := by
  rw [B.A.mul_act, gt_comp1_comp1 _ _ (constantCoeff_act_eq_zero B b) x hx]

theorem constantCoeff_foldr_eq_zero {n : ℕ} (l : List (Pt V n d)) (hl : ∀ x ∈ l, GP x) : GP (l.foldr (addOf B.G.F) 0) := by
  induction l with
  | nil => exact gp_zero₂
  | cons a l ih =>
    exact gp_addOf _ B.G.const _ _ (hl a (by simp)) (ih fun x hx => hl x (by simp [hx]))

theorem map_foldr {n : ℕ} {Q : Type} [AddCommGroup Q] (f : Pt V n d → Q) (f0 : f 0 = 0)
    (fadd : ∀ x y, GP x → GP y → f (addOf B.G.F x y) = f x + f y) (l : List (Pt V n d)) (hl : ∀ x ∈ l, GP x) :
    f (l.foldr (addOf B.G.F) 0) = (l.map f).sum := by
  induction l with
  | nil => exact f0
  | cons a l ih =>
    have hl' : ∀ x ∈ l, GP x := fun x hx => hl x (by simp [hx])
    rw [List.foldr_cons, fadd _ _ (hl a (by simp)) (constantCoeff_foldr_eq_zero B l hl'), ih hl', List.map_cons, List.sum_cons]

def sumP {n m : ℕ} (y : Fin m → Pt V n d) : Pt V n d := (List.ofFn y).foldr (addOf B.G.F) 0

theorem constantCoeff_ofFn_eq_zero {n m : ℕ} {y : Fin m → Pt V n d} (hy : ∀ j, GP (y j)) : ∀ x ∈ List.ofFn y, GP x := by
  intro x hx
  obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hx
  exact hy j

theorem constantCoeff_sumP_eq_zero {n m : ℕ} {y : Fin m → Pt V n d} (hy : ∀ j, GP (y j)) : GP (sumP B y) :=
  constantCoeff_foldr_eq_zero B _ (constantCoeff_ofFn_eq_zero hy)

theorem map_sumP {n m : ℕ} {Q : Type} [AddCommGroup Q] (f : Pt V n d → Q) (f0 : f 0 = 0)
    (fadd : ∀ x y, GP x → GP y → f (addOf B.G.F x y) = f x + f y) {y : Fin m → Pt V n d} (hy : ∀ j, GP (y j)) :
    f (sumP B y) = ∑ j, f (y j) := by
  rw [sumP, map_foldr B f f0 fadd _ (constantCoeff_ofFn_eq_zero hy), List.map_ofFn, List.sum_ofFn]
  rfl

variable {B}

theorem hq_sum (hh : B.IsCanonGauge K h) (w0 : O) {n m : ℕ} (mu : Matrix (Fin n) (Fin n) O) (N : ℕ)
    (hmu : ∀ j k, ∑ i, star (mu i j) * mu i k = if j = k then (N : O) else 0)
    (x : Fin n → Pt V m d) (hx : ∀ j, GP (x j)) :
    ∑ i, hq K hi h (sumP B fun j => comp1 (B.A.act (mu i j)) (x j))
        (comp1 (B.A.act w0) (sumP B fun j => comp1 (B.A.act (mu i j)) (x j))) =
      N • ∑ j, hq K hi h (x j) (comp1 (B.A.act w0) (x j)) := by
  have ha : ∀ (a : O) {y : Pt V m d}, GP y → GP (comp1 (B.A.act a) y) :=
    fun a y hy => gp_comp1 _ _ (constantCoeff_act_eq_zero B a) hy
  let φ : Fin n → Fin n → (O →+ (PS K m d ⧸ intLog K hi m d)) := fun j k =>
    AddMonoidHom.mk' (fun a => hq K hi h (x j) (comp1 (B.A.act a) (x k))) fun a b => by
      rw [add_act B a b (hx k), hq_add_right hi hh (hx j) (ha a (hx k)) (ha b (hx k))]
  have e1 : ∀ i, hq K hi h (sumP B fun j => comp1 (B.A.act (mu i j)) (x j))
        (comp1 (B.A.act w0) (sumP B fun j => comp1 (B.A.act (mu i j)) (x j))) =
      ∑ j, ∑ k, φ j k (star (mu i j) * mu i k * w0) := by
    intro i
    have hy : ∀ j, GP (comp1 (B.A.act (mu i j)) (x j)) := fun j => ha _ (hx j)
    have hs := ha w0 (constantCoeff_sumP_eq_zero B hy)
    rw [map_sumP B (fun y => hq K hi h y _) (hq_zero_left hi hh hs)
      (fun a b h1 h2 => hq_add_left hi hh h1 h2 hs) hy]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_sumP B (fun y => hq K hi h _ (comp1 (B.A.act w0) y))
      (by rw [gt_comp1_zero _ (constantCoeff_act_eq_zero B w0)]; exact hq_zero_right hi hh (hy j))
      (fun a b h1 h2 => by
        rw [act_addOf B w0 h1 h2]; exact hq_add_right hi hh (hy j) (ha _ h1) (ha _ h2)) hy]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hq_act hi hh _ (hx j) (ha _ (hy k)), ← mul_act B _ _ (hx k), ← mul_act B _ _ (hx k)]
    change _ = hq K hi h (x j) (comp1 (B.A.act (star (mu i j) * mu i k * w0)) (x k))
    congr 3
    ring
  rw [Finset.sum_congr rfl fun i _ => e1 i, Finset.sum_comm, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  have e2 : ∀ k, ∑ i, φ j k (star (mu i j) * mu i k * w0) = if j = k then N • φ j k w0 else 0 := by
    intro k
    rw [← map_sum, ← Finset.sum_mul, hmu j k]
    split_ifs
    · rw [← nsmul_eq_mul, map_nsmul]
    · rw [zero_mul, map_zero]
  rw [Finset.sum_congr rfl fun k _ => e2 k, Finset.sum_ite_eq]
  simp [φ]

theorem ev_hL (w0 : O) {n : ℕ} {y : Pt V n d} (hy : GP y) :
    ev ![mp K y] (B.hL K h w0) = ev ![mp K y, mp K (comp1 (B.A.act w0) y)] h := by
  have hA := single_point_zero_constant (constantCoeff_baseChange_eq_zero K hy)
  have p0 : GP (pt K (n := 1) d 0) := gp_pt 0
  rw [FB.hL, germEv_germEv_two_points K _ hA p0 (gp_comp1 _ _ (constantCoeff_actK_eq_zero B K w0) p0), evP_comp1 _ hA _ _ p0, evP_pt _ hA,
    mp_comp1 K _ hy]
  rfl

end Gauge

section Complete
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V]
  [CharZero V] {d : ℕ} {O : Type} [CommRing O] [StarRing O] (B : FB V d O)

theorem evV_eq_ev {m n : ℕ} (a : Fin m → Pt V n d) (ha : ∀ j, GP (a j)) (f : PS V m d) : evV a f = ev a f :=
  (evC_spec V (Fin m × Fin d) (Fin n × Fin d) Unit (fun p => a p.1 p.2)
    (fun p => by rw [ha p.1 p.2]; exact Ideal.zero_mem _)).2.2.1 (fun p => ha p.1 p.2) f

theorem foldr_addV {n : ℕ} (l : List (Pt V n d)) (hl : ∀ x ∈ l, GP x) :
    l.foldr (addV B.G.F) 0 = l.foldr (addOf B.G.F) 0 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have hl' : ∀ x ∈ l, GP x := fun x hx => hl x (by simp [hx])
    rw [List.foldr_cons, List.foldr_cons, ih hl']
    funext i
    exact evV_eq_ev _ (pair_points_zero_constant (hl a (by simp)) (constantCoeff_foldr_eq_zero B l hl')) _

theorem matV_eq_sumP {n m : ℕ} (mu : Matrix (Fin n) (Fin n) O) (x : Fin n → Pt V m d) (hx : ∀ j, GP (x j))
    (i : Fin n) : matV B mu x i = sumP B fun j => comp1 (B.A.act (mu i j)) (x j) := by
  have e : (fun j => compV (B.A.act (mu i j)) (x j)) = fun j => comp1 (B.A.act (mu i j)) (x j) := by
    funext j c
    exact evV_eq_ev _ (single_point_zero_constant (hx j)) _
  rw [matV, e, sumP]
  exact foldr_addV B _ (constantCoeff_ofFn_eq_zero fun j => gp_comp1 _ _ (constantCoeff_act_eq_zero B _) (hx j))

end Complete

end GlobalTheory.PlaceInt.Kappa

open GlobalTheory.PlaceInt.Kappa in
theorem GlobalTheory.PlaceInt.exists_isKappa : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB V d O) (K : Type) [Field K] [Algebra ℚ K] [Algebra V K] [IsFractionRing V K] (h : PS K 2 d) (w0 : O), B.IsCanonGauge K h → ∀ (n : ℕ) (mu : Matrix (Fin n) (Fin n) O) (N : ℕ), (∀ j k, ∑ i, star (mu i j) * mu i k = if j = k then (N : O) else 0) → ∃ κ : PS V n d, IsKappa B K h w0 mu N κ ∧ MvPowerSeries.constantCoeff κ = 1 := by
  intro V _ _ _ _ _ d O _ _ B K _ _ _ _ h w0 hh n mu N hmu
  have hi : Function.Injective (algebraMap V K) := IsFractionRing.injective V K
  have hx : ∀ j : Fin n, GP (pt V (n := n) d j) := fun j => gp_pt j
  have key := hq_sum hi hh w0 mu N hmu (fun j => pt V (n := n) d j) hx
  have hmem : (∑ b : Fin n, ev (n := n) ![fun i => FB.toK K (matV B mu (fun j => pt V (n := n) d j) b i)] (B.hL K h w0)
      - (N : K) • ∑ b : Fin n, ev (n := n) ![pt K d b] (B.hL K h w0)) ∈ intLog K hi n d := by
    rw [← QuotientAddGroup.eq_zero_iff, ← QuotientAddGroup.mk'_apply, map_sub, sub_eq_zero, Nat.cast_smul_eq_nsmul,
      map_nsmul, map_sum, map_sum]
    convert key using 2 with b _
    · rw [matV_eq_sumP B mu _ hx b, hq,
        ← ev_hL w0 (constantCoeff_sumP_eq_zero B fun j => gp_comp1 _ _ (constantCoeff_act_eq_zero B _) (hx j))]
      rfl
    · refine Finset.sum_congr rfl fun b _ => ?_
      rw [hq, ← ev_hL w0 (hx b), mp_pt]
  obtain ⟨h0, κ, hκ⟩ := hmem
  exact ⟨κ, hκ, cc_eq_one K hi _ h0 κ hκ⟩
