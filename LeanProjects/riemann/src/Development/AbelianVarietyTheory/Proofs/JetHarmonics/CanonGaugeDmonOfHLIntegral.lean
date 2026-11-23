import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ChartChg
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FormalSecondPointDerivativeSecondCoordinate

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open GlobalTheory.QuadDeriv

namespace GlobalTheory.GaugeInt

variable {R k : Type} [CommRing R] [CommRing k] (φ : R →+* k) {d : ℕ}

def IntS (n d : ℕ) : Subring (PS k n d) := (MvPowerSeries.map (σ := Fin n × Fin d) φ).range

def IP {n : ℕ} (a : Pt k n d) : Prop := ∃ a' : Pt R n d, GP a' ∧ mapP φ a' = a

def DI {n : ℕ} (f : PS k n d) : Prop := ∀ s, pderiv k s f ∈ IntS φ n d

variable {φ}

theorem IP.gp {n : ℕ} {a : Pt k n d} (h : IP φ a) : GP a := by
  obtain ⟨a', h1, rfl⟩ := h
  exact constantCoeff_mapP_eq_zero φ a' h1

theorem IP.int {n : ℕ} {a : Pt k n d} (h : IP φ a) (i : Fin d) : a i ∈ IntS φ n d := by
  obtain ⟨a', -, rfl⟩ := h
  exact ⟨a' i, rfl⟩

theorem ip_pt {n : ℕ} (j : Fin n) : IP φ (pt k d j) := ⟨pt R d j, gp_pt j, baseChange_pt φ j⟩

theorem ip_zero {n : ℕ} : IP φ (0 : Pt k n d) := ⟨0, gp_zero₂, funext fun _ => map_zero _⟩

theorem ip1 {n : ℕ} {a : Pt k n d} (ha : IP φ a) : ∀ j, IP φ (![a] j) := by
  intro j; fin_cases j; exact ha

theorem ip2 {n : ℕ} {a b : Pt k n d} (ha : IP φ a) (hb : IP φ b) : ∀ j, IP φ (![a, b] j) := by
  intro j; fin_cases j; exacts [ha, hb]

theorem ip3 {n : ℕ} {a b c : Pt k n d} (ha : IP φ a) (hb : IP φ b) (hc : IP φ c) :
    ∀ j, IP φ (![a, b, c] j) := by
  intro j; fin_cases j; exacts [ha, hb, hc]

theorem int_C {n : ℕ} {r : k} (hr : r ∈ φ.range) : (C r : PS k n d) ∈ IntS φ n d := by
  obtain ⟨r, rfl⟩ := hr
  exact ⟨C r, MvPowerSeries.map_C φ r⟩

theorem int_const {n : ℕ} {f : PS k n d} (hf : f ∈ IntS φ n d) : constantCoeff f ∈ φ.range := by
  obtain ⟨f, rfl⟩ := hf
  exact ⟨constantCoeff f, by simp⟩

theorem int_pderiv {n : ℕ} {f : PS k n d} (hf : f ∈ IntS φ n d) : DI φ f := by
  obtain ⟨f, rfl⟩ := hf
  exact fun s => ⟨pderiv R s f, (GlobalTheory.FormalCalc.pderiv_map φ s f).symm⟩

theorem int_ev {m n : ℕ} {V : Fin m → Pt k n d} (hV : ∀ j, IP φ (V j)) {f : PS k m d}
    (hf : f ∈ IntS φ m d) : ev V f ∈ IntS φ n d := by
  obtain ⟨f, rfl⟩ := hf
  choose V' h1 h2 using hV
  obtain rfl : V = fun j => mapP φ (V' j) := funext fun j => (h2 j).symm
  exact ⟨ev V' f, map_ev φ V' h1 f⟩

theorem ip_evP {m n : ℕ} {V : Fin m → Pt k n d} (hV : ∀ j, IP φ (V j)) {a : Pt k m d}
    (ha : IP φ a) : IP φ (evP V a) := by
  obtain ⟨a, h0, rfl⟩ := ha
  choose V' h1 h2 using hV
  obtain rfl : V = fun j => mapP φ (V' j) := funext fun j => (h2 j).symm
  exact ⟨evP V' a, gp_evP V' h1 a h0, funext fun i => map_ev φ V' h1 (a i)⟩

theorem ip_comp1 {n : ℕ} {w : Pt k 1 d} {a : Pt k n d} (hw : IP φ w) (ha : IP φ a) :
    IP φ (comp1 w a) := ip_evP (ip1 ha) hw

theorem ip_addOf {n : ℕ} {F : Pt k 2 d} {a b : Pt k n d} (hF : IP φ F) (ha : IP φ a) (hb : IP φ b) :
    IP φ (addOf F a b) := ip_evP (ip2 ha hb) hF

theorem ip_up {a : Pt k 2 d} (ha : IP φ a) : IP φ (up a) := ip_evP (ip2 (ip_pt 0) (ip_pt 1)) ha

theorem di_ev {m n : ℕ} {V : Fin m → Pt k n d} (hV : ∀ j, IP φ (V j)) {f : PS k m d}
    (hf : DI φ f) : DI φ (ev V f) := by
  intro s
  rw [pderiv_ev V fun j => (hV j).gp]
  exact sum_mem fun j _ => sum_mem fun i _ =>
    mul_mem (int_ev hV (hf _)) (int_pderiv ((hV j).int i) s)

theorem di_of_exp [Algebra ℚ k] {n : ℕ} (p : PS R n d) (hp : constantCoeff p = 1) (a : PS k n d)
    (ha : constantCoeff a = 0) (h : MvPowerSeries.map φ p = FB.expS k a) : DI φ a := by
  intro s
  have h1 : pderiv k s (FB.expS k a) = FB.expS k a * pderiv k s a := by
    unfold FB.expS
    rw [GlobalTheory.FormalCalc.pderiv_powerSeries_subst (PowerSeries.HasSubst.of_constantCoeff_zero ha),
      PowerSeries.derivative_exp]
  have h2 := MvPowerSeries.mul_invOfUnit p 1 (by simpa using hp)
  refine ⟨invOfUnit p 1 * pderiv R s p, ?_⟩
  rw [map_mul, ← GlobalTheory.FormalCalc.pderiv_map, h, h1, ← h, ← mul_assoc, ← map_mul, mul_comm (invOfUnit p 1),
    h2, map_one, one_mul]

theorem dy_sub (v : Fin d → k) (f g : PS k 2 d) : dy v (f - g) = dy v f - dy v g := by
  simp only [dy, map_sub, gt_ev_sub _ hX0, mul_sub, Finset.sum_sub_distrib]

theorem dy_int {v : Fin d → k} (hv : ∀ i, v i ∈ φ.range) {f : PS k 2 d} (hf : DI φ f) :
    dy v f ∈ IntS φ 1 d :=
  sum_mem fun i _ => mul_mem (int_C (hv i)) (int_ev (ip2 (ip_pt 0) ip_zero) (hf _))

theorem lin_int {v : Fin d → k} (hv : ∀ i, v i ∈ φ.range) {f : PS k 1 d} (hf : f ∈ IntS φ 1 d) :
    lin v f ∈ φ.range :=
  sum_mem fun i _ => mul_mem (hv i) (int_const (int_pderiv hf _))

theorem dof_int {F : Pt k 2 d} (hF : IP φ F) {v : Fin d → k} (hv : ∀ i, v i ∈ φ.range)
    {f : PS k 1 d} (hf : f ∈ IntS φ 1 d) : Dof F v f ∈ IntS φ 1 d :=
  sum_mem fun j _ => mul_mem (dy_int hv (int_pderiv (hF.int j))) (int_pderiv hf _)

theorem dof_sub (F : Pt k 2 d) (v : Fin d → k) (f g : PS k 1 d) :
    Dof F v (f - g) = Dof F v f - Dof F v g := by
  simp only [← GE.dofD_apply, map_sub]

theorem dof_almost_additive {F : Pt k 2 d} (hF : GP F)
    (hU : evP (n := 1) ![pt k d 0, 0] F = pt k d 0) {v : Fin d → k} (hv : ∀ i, v i ∈ φ.range)
    (f : PS k 1 d)
    (hf : ev (n := 2) ![pt k d 0] f + ev (n := 2) ![pt k d 1] f - ev ![F] f ∈ IntS φ 2 d) :
    Dof F v f - C (lin v f) ∈ IntS φ 1 d := by
  have h := neg_mem (dy_int hv (int_pderiv hf))
  rwa [dy_sub, dy_add, formalSecondPointDerivative_subst_first_point, formalSecondPointDerivative_subst_second_point, zero_add, neg_sub, ← dof_eq F hF hU] at h

def defL (F : Pt k 2 d) (g : PS k 2 d) : PS k 3 d :=
  ev (n := 3) ![pt k d 0, pt k d 2] g + ev (n := 3) ![pt k d 1, pt k d 2] g -
    ev (n := 3) ![addOf F (pt k d 0) (pt k d 1), pt k d 2] g

def defR (F : Pt k 2 d) (g : PS k 2 d) : PS k 3 d :=
  ev (n := 3) ![pt k d 0, pt k d 1] g + ev (n := 3) ![pt k d 0, pt k d 2] g -
    ev (n := 3) ![pt k d 0, addOf F (pt k d 1) (pt k d 2)] g

theorem ev_defL (F : Pt k 2 d) (hF : GP F) (g : PS k 2 d)
    {n : ℕ} (a b c : Pt k n d) (ha : GP a) (hb : GP b) (hc : GP c) :
    ev ![a, b, c] (defL F g) = ev ![a, c] g + ev ![b, c] g - ev ![addOf F a b, c] g := by
  have hV := triple_points_zero_constant ha hb hc
  have hp : ∀ j : Fin 3, GP (pt k d j) := gp_pt
  rw [defL, gt_ev_sub _ hV, gt_ev_add _ hV, gt_ev_ev' _ _ hV (pair_points_zero_constant (hp _) (hp _)),
    gt_ev_ev' _ _ hV (pair_points_zero_constant (hp _) (hp _)),
    gt_ev_ev' _ _ hV (pair_points_zero_constant (gp_addOf F hF _ _ (hp _) (hp _)) (hp _)), eval_pair_points, eval_pair_points, eval_pair_points,
    evP_addOf _ hV F _ _ (hp _) (hp _)]
  simp only [evP_pt _ hV]
  rfl

theorem ev_defR (F : Pt k 2 d) (hF : GP F) (g : PS k 2 d)
    {n : ℕ} (a b c : Pt k n d) (ha : GP a) (hb : GP b) (hc : GP c) :
    ev ![a, b, c] (defR F g) = ev ![a, b] g + ev ![a, c] g - ev ![a, addOf F b c] g := by
  have hV := triple_points_zero_constant ha hb hc
  have hp : ∀ j : Fin 3, GP (pt k d j) := gp_pt
  rw [defR, gt_ev_sub _ hV, gt_ev_add _ hV, gt_ev_ev' _ _ hV (pair_points_zero_constant (hp _) (hp _)),
    gt_ev_ev' _ _ hV (pair_points_zero_constant (hp _) (hp _)),
    gt_ev_ev' _ _ hV (pair_points_zero_constant (hp _) (gp_addOf F hF _ _ (hp _) (hp _))), eval_pair_points, eval_pair_points, eval_pair_points,
    evP_addOf _ hV F _ _ (hp _) (hp _)]
  simp only [evP_pt _ hV]
  rfl

theorem dz_defL {F : Pt k 2 d} (hF : IP φ F) (g : PS k 2 d) (h : DI φ (defL F g))
    {a b : Pt k 2 d} (ha : IP φ a) (hb : IP φ b) (i : Fin d) :
    ev ![a, 0] (pderiv k ((1 : Fin 2), i) g) + ev ![b, 0] (pderiv k ((1 : Fin 2), i) g) -
      ev ![addOf F a b, 0] (pderiv k ((1 : Fin 2), i) g) ∈ IntS φ 2 d := by
  have e : up (addOf F a b) = addOf F (up a) (up b) := evP_addOf _ hUp F _ _ ha.gp hb.gp
  rw [← dz_right g _ (ip_addOf hF ha hb).gp, ← dz_right g _ ha.gp, ← dz_right g _ hb.gp,
    ← gt_ev_add _ hDown, ← gt_ev_sub _ hDown, ← map_add, ← map_sub, e,
    ← ev_defL F hF.gp g _ _ _ (constantCoeff_up_eq_zero₂ ha.gp) (constantCoeff_up_eq_zero₂ hb.gp) (gp_pt 2)]
  exact int_ev (ip3 (ip_pt 0) (ip_pt 1) ip_zero) (di_ev (ip3 (ip_up ha) (ip_up hb) (ip_pt 2)) h _)

theorem dz_defR {F : Pt k 2 d} (hF : IP φ F) (g : PS k 2 d) (h : DI φ (defR F g))
    {a b : Pt k 2 d} (ha : IP φ a) (hb : IP φ b) (i : Fin d) :
    ev ![0, a] (pderiv k ((0 : Fin 2), i) g) + ev ![0, b] (pderiv k ((0 : Fin 2), i) g) -
      ev ![0, addOf F a b] (pderiv k ((0 : Fin 2), i) g) ∈ IntS φ 2 d := by
  have e : up (addOf F a b) = addOf F (up a) (up b) := evP_addOf _ hUp F _ _ ha.gp hb.gp
  rw [← dz_left g _ (ip_addOf hF ha hb).gp, ← dz_left g _ ha.gp, ← dz_left g _ hb.gp,
    ← gt_ev_add _ hDown, ← gt_ev_sub _ hDown, ← map_add, ← map_sub, e,
    ← ev_defR F hF.gp g _ _ _ (gp_pt 2) (constantCoeff_up_eq_zero₂ ha.gp) (constantCoeff_up_eq_zero₂ hb.gp)]
  exact int_ev (ip3 (ip_pt 0) (ip_pt 1) ip_zero) (di_ev (ip3 (ip_pt 2) (ip_up ha) (ip_up hb)) h _)

theorem quad_int {F : Pt k 2 d} (iF : IP φ F) (hU : evP (n := 1) ![pt k d 0, 0] F = pt k d 0)
    {w : Pt k 1 d} (iw : IP φ w)
    (hom : comp1 w F = addOf F (comp1 w (pt k (n := 2) d 0)) (comp1 w (pt k (n := 2) d 1)))
    (g : PS k 2 d) (c1 : ∀ s, constantCoeff (pderiv k s g) = 0)
    (hl : DI φ (defL F g)) (hr : DI φ (defR F g)) {u v : Fin d → k} (hu : ∀ i, u i ∈ φ.range)
    (hv : ∀ i, v i ∈ φ.range) :
    Dof F u (Dof F v (ev (n := 1) ![pt k d 0, w] g)) -
      C (∑ j, (∑ l, v l * coeff (Finsupp.single ((0 : Fin 1), l) 1) (w j)) *
          (∑ i, u i * coeff (Finsupp.single ((0 : Fin 2), i) 1 + Finsupp.single ((1 : Fin 2), j) 1) g) +
        ∑ i, v i * ∑ l, u l * ∑ j,
          coeff (Finsupp.single ((0 : Fin 2), i) 1 + Finsupp.single ((1 : Fin 2), j) 1) g *
            coeff (Finsupp.single ((0 : Fin 1), l) 1) (w j)) ∈ IntS φ 1 d := by
  have hF := iF.gp
  have hw := iw.gp
  have ip0 : IP φ (pt k (n := 2) d 0) := ip_pt 0
  have ip1' : IP φ (pt k (n := 2) d 1) := ip_pt 1
  have iw0 := ip_comp1 iw ip0
  have iw1 := ip_comp1 iw ip1'
  have p0 : GP (pt k (n := 2) d 0) := gp_pt 0
  have p1 : GP (pt k (n := 2) d 1) := gp_pt 1
  have q0 : GP (pt k (n := 1) d 0) := gp_pt 0
  have w0 := gp_comp1 w _ hw p0
  have w1 := gp_comp1 w _ hw p1
  have e0 : evP (n := 1) ![pt k d 0, 0] (pt k d 0) = pt k d 0 := evP_pt _ hX0 0
  have e1 : evP (n := 1) ![pt k d 0, 0] (pt k d 1) = 0 := evP_pt _ hX0 1
  have f0 : evP (n := 1) ![pt k d 0, 0] (comp1 w (pt k d 0)) = w := by
    rw [evP_comp1 _ hX0 _ _ p0, e0, gt_comp1_pt_right]
  have f1 : evP (n := 1) ![pt k d 0, 0] (comp1 w (pt k d 1)) = 0 := by
    rw [evP_comp1 _ hX0 _ _ p1, e1, gt_comp1_zero w hw]
  have g0 : ∀ v i, dy v (comp1 w (pt k d 0) i) = 0 := fun v i => formalSecondPointDerivative_subst_first_point v _
  have g1 : ∀ v i, dy v (comp1 w (pt k d 1) i) = C (lin v (w i)) := fun v i => formalSecondPointDerivative_subst_second_point v _
  have z : ∀ s, ev (n := 1) ![0, 0] (pderiv k s g) = 0 := fun s => by
    rw [ev_zero_pts _ (by intro j; fin_cases j <;> rfl), c1, map_zero]
  obtain ⟨E, hE, hD⟩ : ∃ E ∈ IntS φ 1 d, Dof F v (ev (n := 1) ![pt k d 0, w] g) =
      ∑ j, C (lin v (w j)) * ev (n := 1) ![pt k d 0, 0] (pderiv k ((1 : Fin 2), j) g) +
      ∑ i, C (v i) * ev (n := 1) ![0, w] (pderiv k ((0 : Fin 2), i) g) - E := by
    refine ⟨_, add_mem (add_mem (dy_int hv (di_ev (ip3 ip0 ip1' (ip_addOf iF iw0 iw1)) hl))
      (dy_int hv (di_ev (ip3 ip0 iw0 iw1) hr))) (dy_int hv (di_ev (ip3 ip1' iw0 iw1) hr)), ?_⟩
    rw [dof_eq F hF hU, formalSubst_single_of_formalSubst_two F hF _ _ q0 hw, gt_comp1_pt F hF, hom,
      ev_defL F hF g _ _ _ p0 p1 (gp_addOf F hF _ _ w0 w1), ev_defR F hF g _ _ _ p0 w0 w1,
      ev_defR F hF g _ _ _ p1 w0 w1, addOf_pt]
    simp only [dy_sub, dy_add]
    rw [formalSecondPointDerivative_formalSubst_two v _ _ p0 w0, formalSecondPointDerivative_formalSubst_two v _ _ p0 w1, formalSecondPointDerivative_formalSubst_two v _ _ p1 w0, formalSecondPointDerivative_formalSubst_two v _ _ p1 w1]
    simp only [e0, e1, f0, f1, g0, g1, formalSecondPointDerivative_first_coordinate, formalSecondPointDerivative_second_coordinate, z, zero_mul, mul_zero, Finset.sum_const_zero,
      zero_add, add_zero]
    ring
  have hb : ∀ j, Dof F u (ev (n := 1) ![pt k d 0, 0] (pderiv k ((1 : Fin 2), j) g)) -
      C (∑ i, u i * coeff (Finsupp.single ((0 : Fin 2), i) 1 + Finsupp.single ((1 : Fin 2), j) 1) g)
        ∈ IntS φ 1 d := by
    intro j
    have h := dof_almost_additive hF hU hu (ev (n := 1) ![pt k d 0, 0] (pderiv k ((1 : Fin 2), j) g)) (by
      rw [formalSubst_single_of_formalSubst_two _ hF _ _ q0 gp_zero₂, formalSubst_single_of_formalSubst_two _ p0 _ _ q0 gp_zero₂,
        formalSubst_single_of_formalSubst_two _ p1 _ _ q0 gp_zero₂, gt_comp1_pt _ hF, gt_comp1_pt _ p0, gt_comp1_pt _ p1,
        formalComp_zero_left_point _ hF, formalComp_zero_left_point _ p0, formalComp_zero_left_point _ p1]
      have := dz_defL iF g hl ip0 ip1' j
      rwa [addOf_pt] at this)
    convert h using 3
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [constantCoeff_pderiv_formalSubst_two _ _ q0 gp_zero₂]
    simp [pderiv_pt_self, const_pderiv_pderiv, apply_ite]
  have ha : ∀ i, Dof F u (ev (n := 1) ![0, w] (pderiv k ((0 : Fin 2), i) g)) -
      C (∑ l, u l * ∑ j,
        coeff (Finsupp.single ((0 : Fin 2), i) 1 + Finsupp.single ((1 : Fin 2), j) 1) g *
          coeff (Finsupp.single ((0 : Fin 1), l) 1) (w j)) ∈ IntS φ 1 d := by
    intro i
    have h := dof_almost_additive hF hU hu (ev (n := 1) ![0, w] (pderiv k ((0 : Fin 2), i) g)) (by
      rw [formalSubst_single_of_formalSubst_two _ hF _ _ gp_zero₂ hw, formalSubst_single_of_formalSubst_two _ p0 _ _ gp_zero₂ hw,
        formalSubst_single_of_formalSubst_two _ p1 _ _ gp_zero₂ hw,
        formalComp_zero_left_point _ hF, formalComp_zero_left_point _ p0, formalComp_zero_left_point _ p1, hom]
      exact dz_defR iF g hr iw0 iw1 i)
    convert h using 3
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [constantCoeff_pderiv_formalSubst_two _ _ gp_zero₂ hw]
    simp only [Pi.zero_apply, map_zero, mul_zero, Finset.sum_const_zero, zero_add]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [GlobalTheory.FormalCalc.pderiv_comm, const_pderiv_pderiv, const_pderiv]
  have h := sub_mem (add_mem
    (sum_mem (t := Finset.univ) fun j _ => mul_mem (int_C (lin_int hv (iw.int j))) (hb j))
    (sum_mem (t := Finset.univ) fun i _ => mul_mem (int_C (hv i)) (ha i))) (dof_int iF hu hE)
  convert h using 1
  rw [hD, dof_sub, GE.dof_add, GE.dof_sum, GE.dof_sum]
  simp only [GE.dof_C_mul, mul_sub, Finset.sum_sub_distrib, ← map_mul, ← map_sum, map_add, lin,
    const_pderiv]
  ring

end GlobalTheory.GaugeInt

namespace GlobalTheory

open GaugeInt

theorem canonGauge_dmonOf_hL_integral :
    ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k]
      [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h : PS k 2 d), B.IsCanonGauge k h →
      ∀ (w0 : O) (ι : Type) [Fintype ι] (u : ι → Fin d → R),
      (∀ l l', dotProduct (fun i => algebraMap R k (u l i)) ((bilinPart k h).mulVec
        ((dAct k B w0).mulVec (fun i => algebraMap R k (u l' i)))) ∈ (algebraMap R k).range) →
      ∀ m : ι →₀ ℕ, constantCoeff (DmonOf (B.FK k) (fun l i => algebraMap R k (u l i)) m
        (B.hL k h w0)) ∈ (algebraMap R k).range := by
  intro R _ d O _ _ k _ _ _ B g hg w0 ι _ u hβ m
  have iF : IP (algebraMap R k) (B.FK k) := ⟨B.G.F, B.G.const, rfl⟩
  have iw : IP (algebraMap R k) (B.actK k w0) := ⟨B.A.act w0, B.A.const w0, rfl⟩
  have hF := iF.gp
  have hw := iw.gp
  have hU : evP (n := 1) ![pt k d 0, 0] (B.FK k) = pt k d 0 := by
    have := congrArg (mapP (algebraMap R k)) (unit_right B.G)
    rw [baseChange_addOf _ _ _ _ (gp_pt 0) gp_zero₂, baseChange_pt,
      show mapP (algebraMap R k) (0 : Pt R 1 d) = 0 from funext fun i => map_zero _] at this
    exact this
  have hom : comp1 (B.actK k w0) (B.FK k) = addOf (B.FK k) (comp1 (B.actK k w0) (pt k (n := 2) d 0))
      (comp1 (B.actK k w0) (pt k (n := 2) d 1)) := by
    have := congrArg (mapP (algebraMap R k)) (B.A.hom w0)
    rw [FGLaw.add, FGLaw.add, addOf_pt, baseChange_comp1 _ _ _ B.G.const,
      baseChange_addOf _ _ _ _ (gp_comp1 _ _ (B.A.const w0) (gp_pt 0))
        (gp_comp1 _ _ (B.A.const w0) (gp_pt 1)),
      baseChange_comp1 _ _ _ (gp_pt 0), baseChange_comp1 _ _ _ (gp_pt 1), baseChange_pt, baseChange_pt] at this
    exact this
  have c0 : constantCoeff g = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply]
    exact coeff_eq_zero_of_axes g hg.ax0 hg.ax1 0 (by simp)
  have c1 : ∀ s, constantCoeff (pderiv k s g) = 0 := fun s => by
    rw [const_pderiv]
    exact coeff_eq_zero_of_axes g hg.ax0 hg.ax1 _ (by simp)
  have hp : ∀ j : Fin 3, GP (pt k d j) := gp_pt
  have hl : DI (algebraMap R k) (defL (B.FK k) g) := by
    refine di_of_exp B.ph1 ?_ _ ?_ hg.ph1
    · rw [← gt_const_ev_eq _ (triple_points_zero_constant (n := 2) gp_zero₂ (gp_pt 0) (gp_pt 1)), B.cocycleLeft_zero_fst, map_one]
    · rw [defL, map_sub, map_add, gt_const_ev _ (pair_points_zero_constant (hp _) (hp _)) _ c0,
        gt_const_ev _ (pair_points_zero_constant (hp _) (hp _)) _ c0,
        gt_const_ev _ (pair_points_zero_constant (gp_addOf _ hF _ _ (hp _) (hp _)) (hp _)) _ c0]
      simp
  have hr : DI (algebraMap R k) (defR (B.FK k) g) := by
    refine di_of_exp B.ph2 ?_ _ ?_ hg.ph2
    · rw [← gt_const_ev_eq _ (triple_points_zero_constant (n := 2) gp_zero₂ (gp_pt 0) (gp_pt 1)), B.cocycleRight_zero_fst, map_one]
    · rw [defR, map_sub, map_add, gt_const_ev _ (pair_points_zero_constant (hp _) (hp _)) _ c0,
        gt_const_ev _ (pair_points_zero_constant (hp _) (hp _)) _ c0,
        gt_const_ev _ (pair_points_zero_constant (hp _) (gp_addOf _ hF _ _ (hp _) (hp _))) _ c0]
      simp
  set U : ι → Fin d → k := fun l i => algebraMap R k (u l i) with hUdef
  have hu : ∀ l i, U l i ∈ (algebraMap R k).range := fun l i => ⟨u l i, rfl⟩
  have hq : B.hL k g w0 = ev (n := 1) ![pt k d 0, B.actK k w0] g := by
    rw [FB.hL, gt_comp1_pt_right]
  have h2 : ∀ l l', Dof (B.FK k) (U l) (Dof (B.FK k) (U l') (B.hL k g w0)) ∈
      IntS (algebraMap R k) 1 d := by
    intro l l'
    have h := add_mem (quad_int iF hU iw hom g c1 hl hr (hu l) (hu l'))
      (int_C (n := 1) (d := d) (add_mem (hβ l l') (hβ l' l)))
    rw [hq]
    convert h using 1
    rw [sub_add_eq_add_sub, eq_sub_iff_add_eq]
    congr 2
    simp only [dotProduct, Matrix.mulVec, bilinPart, dAct, Finset.mul_sum, Finset.sum_mul]
    congr 1
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
        Finset.sum_congr rfl fun l _ => by ring
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring
  let P : PS k 1 d → Prop := fun f => f = B.hL k g w0 ∨
    (∃ l, f = Dof (B.FK k) (U l) (B.hL k g w0)) ∨ f ∈ IntS (algebraMap R k) 1 d
  have hstep : ∀ l f, P f → P (Dof (B.FK k) (U l) f) := by
    rintro l f (rfl | ⟨l', rfl⟩ | hf)
    · exact Or.inr (Or.inl ⟨l, rfl⟩)
    · exact Or.inr (Or.inr (h2 l l'))
    · exact Or.inr (Or.inr (dof_int iF (hu l) hf))
  have hP : P (DmonOf (B.FK k) U m (B.hL k g w0)) := by
    unfold DmonOf
    induction (Finset.univ : Finset ι).toList with
    | nil => exact Or.inl rfl
    | cons a L ih => exact Function.Iterate.rec P ih (hstep a) (m a)
  rcases hP with e | ⟨l, e⟩ | e
  · rw [e, hq, gt_const_ev _ (pair_points_zero_constant (gp_pt 0) hw) _ c0]
    exact zero_mem _
  · rw [e, hq, Dof]
    simp only [map_sum, map_mul, constantCoeff_pderiv_formalSubst_two _ _ (gp_pt 0) hw, c1, zero_mul,
      Finset.sum_const_zero, add_zero, mul_zero]
    exact zero_mem _
  · exact int_const e

end GlobalTheory
