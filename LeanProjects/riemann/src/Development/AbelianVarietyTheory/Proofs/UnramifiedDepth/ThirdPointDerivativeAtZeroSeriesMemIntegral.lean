import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ChartChg
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CanonGaugeDmonOfHLIntegral
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.CoeffSingleLawAdd

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open GlobalTheory.QuadDeriv GlobalTheory.GaugeInt

namespace GlobalTheory.GaugeDiv

variable {R k : Type} [CommRing R] [CommRing k] {φ : R →+* k} {d : ℕ}

def DD (F : Pt k 2 d) (a : Fin 2) (u : Fin d → k) (G : PS k 2 d) : PS k 2 d :=
  ∑ j, ev (n := 2) ![pt k d a] (dy u (F j)) * pderiv k (a, j) G

theorem dd_add (F : Pt k 2 d) (a : Fin 2) (u : Fin d → k) (G H : PS k 2 d) :
    DD F a u (G + H) = DD F a u G + DD F a u H := by
  simp only [DD, map_add, mul_add, Finset.sum_add_distrib]

theorem dd_sub (F : Pt k 2 d) (a : Fin 2) (u : Fin d → k) (G H : PS k 2 d) :
    DD F a u (G - H) = DD F a u G - DD F a u H := by
  simp only [DD, map_sub, mul_sub, Finset.sum_sub_distrib]

theorem dd_natCast_mul (F : Pt k 2 d) (a : Fin 2) (u : Fin d → k) (N : ℕ) (G : PS k 2 d) :
    DD F a u (N * G) = N * DD F a u G := by
  simp only [DD, ← nsmul_eq_mul, map_nsmul, Finset.smul_sum, mul_smul_comm]

theorem dd_int {F : Pt k 2 d} (hF : IP φ F) (a : Fin 2) {v : Fin d → k} (hv : ∀ i, v i ∈ φ.range)
    {G : PS k 2 d} (hG : G ∈ IntS φ 2 d) : DD F a v G ∈ IntS φ 2 d :=
  sum_mem fun j _ => mul_mem (int_ev (ip1 (ip_pt a)) (dy_int hv (int_pderiv (hF.int j))))
    (int_pderiv hG _)

theorem dd_ev_self (F : Pt k 2 d) (a : Fin 2) (v : Fin d → k) (f : PS k 1 d) :
    DD F a v (ev (n := 2) ![pt k d a] f) = ev (n := 2) ![pt k d a] (Dof F v f) := by
  have h : ∀ j, GP ((![pt k d a] : Fin 1 → Pt k 2 d) j) := single_point_zero_constant (gp_pt a)
  rw [DD, Dof, ev_sum _ h]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [gt_ev_mul _ h, pderiv_ev _ h, Fin.sum_univ_one]
  simp [pderiv_pt_self, dy]

theorem dd_ev_ne (F : Pt k 2 d) {a b : Fin 2} (hab : b ≠ a) (v : Fin d → k) (f : PS k 1 d) :
    DD F a v (ev (n := 2) ![pt k d b] f) = 0 := by
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [pderiv_ev_eq_zero _ (single_point_zero_constant (gp_pt b)), mul_zero]
  intro j' i
  fin_cases j'
  exact pderiv_pt_ne hab _ _

theorem ev_formalSecondPointDerivative {n : ℕ} (a : Pt k n d) (ha : GP a) (v : Fin d → k) (f : PS k 2 d) :
    ev ![a] (dy v f) = ∑ i, C (v i) * ev ![a, 0] (pderiv k ((1 : Fin 2), i) f) := by
  rw [dy, ev_sum _ (single_point_zero_constant ha)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [gt_ev_mul _ (single_point_zero_constant ha), ev_C, formalSubst_single_of_formalSubst_two _ ha _ _ (gp_pt 0) gp_zero₂, gt_comp1_pt _ ha,
    formalComp_zero_left_point _ ha]

theorem dof_graph {F : Pt k 2 d} (hF : GP F) (hU : evP (n := 1) ![pt k d 0, 0] F = pt k d 0)
    {w : Pt k 1 d} (hw : GP w)
    (hom : comp1 w F = addOf F (comp1 w (pt k (n := 2) d 0)) (comp1 w (pt k (n := 2) d 1)))
    (u v : Fin d → k) (N : ℕ) (huv : ∀ i, lin u (w i) = N * v i) (G : PS k 2 d) :
    Dof F u (ev (n := 1) ![pt k d 0, w] G) =
      ev (n := 1) ![pt k d 0, w] (DD F 0 u G + N * DD F 1 v G) := by
  have p0 : GP (pt k (n := 2) d 0) := gp_pt 0
  have p1 : GP (pt k (n := 2) d 1) := gp_pt 1
  have q0 : GP (pt k (n := 1) d 0) := gp_pt 0
  have w0 := gp_comp1 w _ hw p0
  have w1 := gp_comp1 w _ hw p1
  have hV := pair_points_zero_constant q0 hw
  have e0 : evP (n := 1) ![pt k d 0, 0] (pt k d 0) = pt k d 0 := evP_pt _ hX0 0
  have e1 : evP (n := 1) ![pt k d 0, 0] (pt k d 1) = 0 := evP_pt _ hX0 1
  have f0 : evP (n := 1) ![pt k d 0, 0] (comp1 w (pt k d 0)) = w := by
    rw [evP_comp1 _ hX0 _ _ p0, e0, gt_comp1_pt_right]
  have f1 : evP (n := 1) ![pt k d 0, 0] (comp1 w (pt k d 1)) = 0 := by
    rw [evP_comp1 _ hX0 _ _ p1, e1, gt_comp1_zero w hw]
  have f2 : evP (n := 1) ![pt k d 0, 0] (comp1 w F) = w := by
    rw [evP_comp1 _ hX0 _ _ hF, hU, gt_comp1_pt_right]
  have g0 : ∀ i, dy u (comp1 w (pt k d 0) i) = 0 := fun i => formalSecondPointDerivative_subst_first_point u _
  have g1 : ∀ i, dy u (comp1 w (pt k d 1) i) = C (lin u (w i)) := fun i => formalSecondPointDerivative_subst_second_point u _
  have key : ∀ j, dy u (comp1 w F j) = N * ev ![w] (dy v (F j)) := by
    intro j
    rw [hom, addOf, formalSecondPointDerivative_formalSubst_two u _ _ w0 w1, ev_formalSecondPointDerivative w hw]
    simp only [g0, g1, f0, f1, huv, zero_mul, Finset.sum_const_zero, zero_add, Finset.mul_sum, map_mul,
      map_natCast, mul_assoc]
  have a0 : ∀ f : PS k 1 d, ev (n := 1) ![pt k d 0, w] (ev (n := 2) ![pt k d 0] f) = f := fun f => by
    rw [gt_ev_ev' _ _ hV (single_point_zero_constant p0), vec1, evP_pt _ hV]
    exact gt_ev_pt_self f
  have a1 : ∀ f : PS k 1 d, ev (n := 1) ![pt k d 0, w] (ev (n := 2) ![pt k d 1] f) = ev ![w] f :=
    fun f => by
      rw [gt_ev_ev' _ _ hV (single_point_zero_constant p1), vec1, evP_pt _ hV]
      rfl
  have hN : ev (n := 1) ![pt k d 0, w] (N : PS k 2 d) = N := by
    rw [← map_natCast (C : k →+* PS k 2 d), ev_C, map_natCast]
  rw [dof_eq F hF hU, formalSubst_single_of_formalSubst_two F hF _ _ q0 hw, gt_comp1_pt F hF,
    formalSecondPointDerivative_formalSubst_two u _ _ hF (gp_comp1 w _ hw hF), hU, f2, gt_ev_add _ hV, gt_ev_mul _ hV, hN, DD, DD,
    ev_sum _ hV, ev_sum _ hV]
  simp only [gt_ev_mul _ hV, a0, a1, key, Finset.mul_sum, mul_assoc]

theorem dd_axis {F : Pt k 2 d} (hF : GP F) (hU : evP (n := 1) ![pt k d 0, 0] F = pt k d 0)
    (u : Fin d → k) {G : PS k 2 d} (hG : ev (n := 1) ![pt k d 0, 0] G = 0) :
    ev (n := 1) ![pt k d 0, 0] (DD F 0 u G) = 0 := by
  have h := dof_graph hF hU gp_zero₂ (by
    rw [formalComp_zero_left_point _ hF, formalComp_zero_left_point _ (gp_pt 0), formalComp_zero_left_point _ (gp_pt 1)]
    funext i
    rw [addOf, ev_zero_pts _ (by intro j; fin_cases j <;> rfl), hF i, map_zero]
    rfl) u 0 0 (by simp [lin]) G
  rw [hG, Nat.cast_zero, zero_mul, add_zero] at h
  rw [← h]
  simp [Dof]

theorem down_addOf {F : Pt k 2 d} (hU : evP (n := 1) ![pt k d 0, 0] F = pt k d 0) (a : Fin 2) :
    evP (n := 2) ![pt k d 0, pt k d 1, 0] (addOf F (up (pt k d a)) (pt k d 2)) = pt k d a := by
  have ha : GP (pt k (n := 2) d a) := gp_pt a
  rw [evP_addOf _ hDown _ _ _ (constantCoeff_up_eq_zero₂ ha) (gp_pt 2), down_up, evP_pt _ hDown]
  have h := congrArg (fun b => comp1 b (pt k (n := 2) d a)) hU
  simp only [gt_comp1_pt _ ha] at h
  rw [← h]
  funext i
  change _ = ev ![pt k d a] (ev ![pt k d 0, 0] (F i))
  rw [formalSubst_single_of_formalSubst_two _ ha _ _ (gp_pt 0) gp_zero₂, gt_comp1_pt _ ha, formalComp_zero_left_point _ ha, h]
  rfl

theorem ev_pts (g : PS k 2 d) : ev (n := 2) ![pt k d 0, pt k d 1] g = g := by
  have e : (fun p : Fin 2 × Fin d => (![pt k (n := 2) d 0, pt k d 1] p.1) p.2) = X := by
    funext p
    obtain ⟨j, i⟩ := p
    fin_cases j <;> rfl
  rw [ev, e, MvPowerSeries.subst_self]
  rfl

def dz3 (v : Fin d → k) (f : PS k 3 d) : PS k 2 d :=
  ∑ i, C (v i) * ev (n := 2) ![pt k d 0, pt k d 1, 0] (pderiv k ((2 : Fin 3), i) f)

theorem thirdPointDerivativeAtZeroSeries_mem_integral {v : Fin d → k} (hv : ∀ i, v i ∈ φ.range) {f : PS k 3 d} (hf : DI φ f) :
    dz3 v f ∈ IntS φ 2 d :=
  sum_mem fun i _ => mul_mem (int_C (hv i)) (int_ev (ip3 (ip_pt 0) (ip_pt 1) ip_zero) (hf _))

theorem thirdPointDerivativeAtZeroSeries_add_sub (v : Fin d → k) (f g h : PS k 3 d) :
    dz3 v (f + g - h) = dz3 v f + dz3 v g - dz3 v h := by
  simp only [dz3, map_add, map_sub, gt_ev_add _ hDown, gt_ev_sub _ hDown, mul_add, mul_sub,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]

theorem thirdPointDerivativeAtZeroSeries_twoPointLift (v : Fin d → k) (g : PS k 2 d) :
    dz3 v (ev ![up (pt k d 0), up (pt k d 1)] g) = 0 := by
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [pderiv_ev_eq_zero _ (pair_points_zero_constant (constantCoeff_up_eq_zero₂ (gp_pt 0)) (constantCoeff_up_eq_zero₂ (gp_pt 1))), gt_ev_zero _ hDown,
    mul_zero]
  intro j l
  fin_cases j <;> exact pderiv_up _ _ _

theorem thirdPointDerivativeAtZeroSeries_addOf_left {F : Pt k 2 d} (hF : GP F) (hU : evP (n := 1) ![pt k d 0, 0] F = pt k d 0)
    (v : Fin d → k) (g : PS k 2 d) :
    dz3 v (ev ![addOf F (up (pt k d 0)) (pt k d 2), up (pt k d 1)] g) = DD F 0 v g := by
  have hA := pair_points_zero_constant (gp_addOf F hF _ _ (constantCoeff_up_eq_zero₂ (gp_pt (k := k) (d := d) 0)) (gp_pt 2))
    (constantCoeff_up_eq_zero₂ (gp_pt 1))
  simp only [dz3, DD, ev_pderiv_ev _ hDown _ hA, Fin.sum_univ_two, eval_pair_points, down_up, down_addOf hU,
    Matrix.cons_val_zero, Matrix.cons_val_one, pderiv_up, gt_ev_zero _ hDown, mul_zero,
    Finset.sum_const_zero, add_zero, ev_pts, addOf, dz_right _ _ (gp_pt 0),
    ev_formalSecondPointDerivative _ (gp_pt 0), Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

theorem thirdPointDerivativeAtZeroSeries_addOf_right {F : Pt k 2 d} (hF : GP F) (hU : evP (n := 1) ![pt k d 0, 0] F = pt k d 0)
    (v : Fin d → k) (g : PS k 2 d) :
    dz3 v (ev ![up (pt k d 0), addOf F (up (pt k d 1)) (pt k d 2)] g) = DD F 1 v g := by
  have hA := pair_points_zero_constant (constantCoeff_up_eq_zero₂ (gp_pt 0))
    (gp_addOf F hF _ _ (constantCoeff_up_eq_zero₂ (gp_pt (k := k) (d := d) 1)) (gp_pt 2))
  simp only [dz3, DD, ev_pderiv_ev _ hDown _ hA, Fin.sum_univ_two, eval_pair_points, down_up, down_addOf hU,
    Matrix.cons_val_zero, Matrix.cons_val_one, pderiv_up, gt_ev_zero _ hDown, mul_zero,
    Finset.sum_const_zero, zero_add, ev_pts, addOf, dz_right _ _ (gp_pt 1),
    ev_formalSecondPointDerivative _ (gp_pt 1), Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

def al (u : Fin d → k) (g : PS k 2 d) : PS k 1 d :=
  ∑ i, C (u i) * ev (n := 1) ![0, pt k d 0] (pderiv k ((0 : Fin 2), i) g)

theorem dd_zero_sub {F : Pt k 2 d} (iF : IP φ F) (hU : evP (n := 1) ![pt k d 0, 0] F = pt k d 0)
    (g : PS k 2 d) (hl : DI φ (defL F g)) {u : Fin d → k} (hu : ∀ i, u i ∈ φ.range) :
    DD F 0 u g - ev (n := 2) ![pt k d 1] (al u g) ∈ IntS φ 2 d := by
  have p0 : GP (pt k (n := 2) d 0) := gp_pt 0
  have p1 : GP (pt k (n := 2) d 1) := gp_pt 1
  have h := neg_mem (thirdPointDerivativeAtZeroSeries_mem_integral hu (di_ev (ip3 (ip_up (ip_pt 0)) (ip_pt 2) (ip_up (ip_pt 1))) hl))
  rw [ev_defL F iF.gp g _ _ _ (constantCoeff_up_eq_zero₂ p0) (gp_pt 2) (constantCoeff_up_eq_zero₂ p1), thirdPointDerivativeAtZeroSeries_add_sub, thirdPointDerivativeAtZeroSeries_twoPointLift,
    thirdPointDerivativeAtZeroSeries_addOf_left iF.gp hU, zero_add, neg_sub] at h
  convert h using 2
  rw [al, dz3, ev_sum _ (single_point_zero_constant p1)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [dz_left g _ p1, gt_ev_mul _ (single_point_zero_constant p1), ev_C, formalSubst_single_of_formalSubst_two _ p1 _ _ gp_zero₂ (gp_pt 0),
    gt_comp1_pt _ p1, formalComp_zero_left_point _ p1]

theorem dd_one_sub {F : Pt k 2 d} (iF : IP φ F) (hU : evP (n := 1) ![pt k d 0, 0] F = pt k d 0)
    (g : PS k 2 d) (hr : DI φ (defR F g)) {v : Fin d → k} (hv : ∀ i, v i ∈ φ.range) :
    DD F 1 v g - ev (n := 2) ![pt k d 0] (dy v g) ∈ IntS φ 2 d := by
  have p0 : GP (pt k (n := 2) d 0) := gp_pt 0
  have p1 : GP (pt k (n := 2) d 1) := gp_pt 1
  have h := neg_mem (thirdPointDerivativeAtZeroSeries_mem_integral hv (di_ev (ip3 (ip_up (ip_pt 0)) (ip_up (ip_pt 1)) (ip_pt 2)) hr))
  rw [ev_defR F iF.gp g _ _ _ (constantCoeff_up_eq_zero₂ p0) (constantCoeff_up_eq_zero₂ p1) (gp_pt 2), thirdPointDerivativeAtZeroSeries_add_sub, thirdPointDerivativeAtZeroSeries_twoPointLift,
    thirdPointDerivativeAtZeroSeries_addOf_right iF.gp hU, zero_add, neg_sub] at h
  convert h using 2
  rw [ev_formalSecondPointDerivative _ p0, dz3]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [dz_right g _ p0]

theorem dof_al {F : Pt k 2 d} (iF : IP φ F) (hU : evP (n := 1) ![pt k d 0, 0] F = pt k d 0)
    (g : PS k 2 d) (hr : DI φ (defR F g)) {u v : Fin d → k} (hu : ∀ i, u i ∈ φ.range)
    (hv : ∀ i, v i ∈ φ.range) (hβ : dotProduct u ((bilinPart k g).mulVec v) ∈ φ.range) :
    Dof F v (al u g) ∈ IntS φ 1 d := by
  have hF := iF.gp
  have p0 : GP (pt k (n := 2) d 0) := gp_pt 0
  have p1 : GP (pt k (n := 2) d 1) := gp_pt 1
  have q0 : GP (pt k (n := 1) d 0) := gp_pt 0
  have ha : ∀ i, Dof F v (ev (n := 1) ![0, pt k d 0] (pderiv k ((0 : Fin 2), i) g)) -
      C ((bilinPart k g).mulVec v i) ∈ IntS φ 1 d := by
    intro i
    have h := dof_almost_additive hF hU hv
      (ev (n := 1) ![0, pt k d 0] (pderiv k ((0 : Fin 2), i) g)) (by
      rw [formalSubst_single_of_formalSubst_two _ hF _ _ gp_zero₂ q0, formalSubst_single_of_formalSubst_two _ p0 _ _ gp_zero₂ q0,
        formalSubst_single_of_formalSubst_two _ p1 _ _ gp_zero₂ q0, gt_comp1_pt _ hF, gt_comp1_pt _ p0, gt_comp1_pt _ p1,
        formalComp_zero_left_point _ hF, formalComp_zero_left_point _ p0, formalComp_zero_left_point _ p1]
      have := dz_defR iF g hr (ip_pt 0) (ip_pt 1) i
      rwa [addOf_pt] at this)
    convert h using 3
    simp only [Matrix.mulVec, dotProduct, lin]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [constantCoeff_pderiv_formalSubst_two _ _ gp_zero₂ q0, mul_comm]
    simp [pderiv_pt_self, apply_ite, GlobalTheory.FormalCalc.pderiv_comm ((1 : Fin 2), l), const_pderiv_pderiv,
      bilinPart]
  have h := add_mem (sum_mem (t := Finset.univ) fun i _ => mul_mem (int_C (hu i)) (ha i))
    (int_C (n := 1) (d := d) hβ)
  convert h using 1
  rw [al, GE.dof_sum]
  simp only [GE.dof_C_mul, mul_sub, Finset.sum_sub_distrib, ← map_mul, ← map_sum, dotProduct]
  ring

theorem dof_dy {F : Pt k 2 d} (iF : IP φ F) (hU : evP (n := 1) ![pt k d 0, 0] F = pt k d 0)
    (g : PS k 2 d) (hl : DI φ (defL F g)) {u v : Fin d → k} (hu : ∀ i, u i ∈ φ.range)
    (hv : ∀ i, v i ∈ φ.range) (hβ : dotProduct u ((bilinPart k g).mulVec v) ∈ φ.range) :
    Dof F u (dy v g) ∈ IntS φ 1 d := by
  have hF := iF.gp
  have p0 : GP (pt k (n := 2) d 0) := gp_pt 0
  have p1 : GP (pt k (n := 2) d 1) := gp_pt 1
  have q0 : GP (pt k (n := 1) d 0) := gp_pt 0
  have hb : ∀ j, Dof F u (ev (n := 1) ![pt k d 0, 0] (pderiv k ((1 : Fin 2), j) g)) -
      C (Matrix.vecMul u (bilinPart k g) j) ∈ IntS φ 1 d := by
    intro j
    have h := dof_almost_additive hF hU hu (ev (n := 1) ![pt k d 0, 0] (pderiv k ((1 : Fin 2), j) g)) (by
      rw [formalSubst_single_of_formalSubst_two _ hF _ _ q0 gp_zero₂, formalSubst_single_of_formalSubst_two _ p0 _ _ q0 gp_zero₂,
        formalSubst_single_of_formalSubst_two _ p1 _ _ q0 gp_zero₂, gt_comp1_pt _ hF, gt_comp1_pt _ p0, gt_comp1_pt _ p1,
        formalComp_zero_left_point _ hF, formalComp_zero_left_point _ p0, formalComp_zero_left_point _ p1]
      have := dz_defL iF g hl (ip_pt 0) (ip_pt 1) j
      rwa [addOf_pt] at this)
    convert h using 3
    simp only [Matrix.vecMul, dotProduct, lin]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [constantCoeff_pderiv_formalSubst_two _ _ q0 gp_zero₂]
    simp [pderiv_pt_self, const_pderiv_pderiv, apply_ite, bilinPart]
  rw [Matrix.dotProduct_mulVec, dotProduct_comm] at hβ
  have h := add_mem (sum_mem (t := Finset.univ) fun j _ => mul_mem (int_C (hv j)) (hb j))
    (int_C (n := 1) (d := d) hβ)
  convert h using 1
  rw [dy, GE.dof_sum]
  simp only [GE.dof_C_mul, mul_sub, Finset.sum_sub_distrib, ← map_mul, ← map_sum, dotProduct]
  ring

theorem dmon_div {F : Pt k 2 d} (iF : IP φ F) (hU : evP (n := 1) ![pt k d 0, 0] F = pt k d 0)
    {w : Pt k 1 d} (hw : GP w)
    (hom : comp1 w F = addOf F (comp1 w (pt k (n := 2) d 0)) (comp1 w (pt k (n := 2) d 1)))
    (g : PS k 2 d) (h1 : ev (n := 1) ![pt k d 0, 0] g = 0)
    (c1 : ∀ s, constantCoeff (pderiv k s g) = 0)
    (hl : DI φ (defL F g)) (hr : DI φ (defR F g)) {ι : Type} [Fintype ι] (U V : ι → Fin d → k)
    (hu : ∀ l i, U l i ∈ φ.range) (hv : ∀ l i, V l i ∈ φ.range) (N : ℕ)
    (huv : ∀ l i, lin (U l) (w i) = N * V l i)
    (hβ : ∀ l l', dotProduct (U l) ((bilinPart k g).mulVec (V l')) ∈ φ.range) (m : ι →₀ ℕ) :
    ∃ r : R, constantCoeff (DmonOf F U m (ev (n := 1) ![pt k d 0, w] g)) = φ (N * r) := by
  have hF := iF.gp
  have hV := pair_points_zero_constant (gp_pt (k := k) (d := d) (n := 1) 0) hw
  let S : PS k 2 d → Prop := fun G => constantCoeff G ∈ φ.range ∧
    ∀ l, DD F 0 (U l) G ∈ IntS φ 2 d ∧ DD F 1 (V l) G ∈ IntS φ 2 d
  have hS : ∀ G ∈ IntS φ 2 d, S G := fun G hG =>
    ⟨int_const hG, fun l => ⟨dd_int iF 0 (hu l) hG, dd_int iF 1 (hv l) hG⟩⟩
  have cD : ∀ a v, constantCoeff (DD F a v g) ∈ φ.range := fun a v => by
    simp only [DD, map_sum, map_mul, c1, mul_zero, Finset.sum_const_zero]
    exact zero_mem _
  have hS0 : ∀ l, S (DD F 0 (U l) g) := by
    intro l
    have h := dd_zero_sub iF hU g hl (hu l)
    refine ⟨cD _ _, fun l' => ⟨?_, ?_⟩⟩
    · have h' := dd_int iF 0 (hu l') h
      rwa [dd_sub, dd_ev_ne F (by decide), sub_zero] at h'
    · have h' := add_mem (dd_int iF 1 (hv l') h)
        (int_ev (ip1 (ip_pt (n := 2) 1)) (dof_al iF hU g hr (hu l) (hv l') (hβ l l')))
      rwa [dd_sub, dd_ev_self, sub_add_cancel] at h'
  have hS1 : ∀ l, S (DD F 1 (V l) g) := by
    intro l
    have h := dd_one_sub iF hU g hr (hv l)
    refine ⟨cD _ _, fun l' => ⟨?_, ?_⟩⟩
    · have h' := add_mem (dd_int iF 0 (hu l') h)
        (int_ev (ip1 (ip_pt (n := 2) 0)) (dof_dy iF hU g hl (hu l') (hv l) (hβ l' l)))
      rwa [dd_sub, dd_ev_self, sub_add_cancel] at h'
    · have h' := dd_int iF 1 (hv l') h
      rwa [dd_sub, dd_ev_ne F (by decide), sub_zero] at h'
  let P : PS k 1 d → Prop := fun f => f = ev (n := 1) ![pt k d 0, w] g ∨
    ∃ A E, S A ∧ S E ∧ ev (n := 1) ![pt k d 0, 0] A = 0 ∧
      f = ev (n := 1) ![pt k d 0, w] (A + N * E)
  have hstep : ∀ l f, P f → P (Dof F (U l) f) := by
    rintro l f (rfl | ⟨A, E, hA, hE, h0, rfl⟩)
    · exact Or.inr ⟨_, _, hS0 l, hS1 l, dd_axis hF hU _ h1, dof_graph hF hU hw hom _ _ N (huv l) g⟩
    · refine Or.inr ⟨DD F 0 (U l) A, DD F 0 (U l) E + DD F 1 (V l) A + N * DD F 1 (V l) E,
        hS _ (hA.2 l).1, hS _ (add_mem (add_mem (hE.2 l).1 (hA.2 l).2)
          (mul_mem (natCast_mem _ N) (hE.2 l).2)), dd_axis hF hU _ h0, ?_⟩
      rw [dof_graph hF hU hw hom _ _ N (huv l), dd_add, dd_add, dd_natCast_mul, dd_natCast_mul]
      congr 1
      ring
  have hP : P (DmonOf F U m (ev (n := 1) ![pt k d 0, w] g)) := by
    unfold DmonOf
    induction (Finset.univ : Finset ι).toList with
    | nil => exact Or.inl rfl
    | cons a L ih => exact Function.Iterate.rec P ih (hstep a) (m a)
  rcases hP with e | ⟨A, E, -, ⟨⟨r, hr⟩, -⟩, h0, e⟩
  · refine ⟨0, ?_⟩
    rw [e, gt_const_ev_eq _ hV, ← gt_const_ev_eq _ hX0, h1]
    simp
  · refine ⟨r, ?_⟩
    rw [e, gt_const_ev_eq _ hV, map_add, ← gt_const_ev_eq _ hX0 A, h0]
    simp [hr]

end GlobalTheory.GaugeDiv

namespace GlobalTheory

open GaugeDiv

theorem canonGauge_dmonOf_hL_natCast_mul :
    ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k]
      [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h : PS k 2 d), B.IsCanonGauge k h →
      ∀ (w : O) (N : ℕ) (ι : Type) [Fintype ι] (u : ι → Fin d → R),
      (∀ l l', dotProduct (fun i => algebraMap R k (u l i)) ((bilinPart k h).mulVec
        ((dAct k B w).mulVec (fun i => algebraMap R k (u l' i)))) ∈ (algebraMap R k).range) →
      ∀ mo : ι →₀ ℕ, ∃ r : R, constantCoeff (DmonOf (B.FK k) (fun l i => algebraMap R k (u l i)) mo
        (B.hL k h ((N : O) * w))) = algebraMap R k (N * r) := by
  intro R _ d O _ _ k _ _ _ B g hg w N ι _ u hβ m
  have iF : IP (algebraMap R k) (B.FK k) := ⟨B.G.F, B.G.const, rfl⟩
  have iw : ∀ a, IP (algebraMap R k) (B.actK k a) := fun a => ⟨B.A.act a, B.A.const a, rfl⟩
  have hF := iF.gp
  have hU : evP (n := 1) ![pt k d 0, 0] (B.FK k) = pt k d 0 := by
    have := congrArg (mapP (algebraMap R k)) (unit_right B.G)
    rw [baseChange_addOf _ _ _ _ (gp_pt 0) gp_zero₂, baseChange_pt,
      show mapP (algebraMap R k) (0 : Pt R 1 d) = 0 from funext fun i => map_zero _] at this
    exact this
  have hom : ∀ w0, comp1 (B.actK k w0) (B.FK k) =
      addOf (B.FK k) (comp1 (B.actK k w0) (pt k (n := 2) d 0))
        (comp1 (B.actK k w0) (pt k (n := 2) d 1)) := by
    intro w0
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
  have hlin : ∀ a (v : Fin d → k) i, lin v (B.actK k a i) = (dAct k B a).mulVec v i := by
    intro a v i
    simp only [lin, const_pderiv, Matrix.mulVec, dotProduct, dAct, mul_comm]
  have hadd := (FormalCalc.dAct_add_and_one R d O k B).1
  have hN : ∀ n : ℕ, dAct k B ((n : O) * w) = n • dAct k B w := by
    intro n
    induction n with
    | zero =>
      have := hadd 0 0
      rw [add_zero, left_eq_add] at this
      simp [this]
    | succ n ih => rw [Nat.cast_succ, add_mul, one_mul, hadd, ih, succ_nsmul]
  rw [FB.hL, gt_comp1_pt_right]
  refine dmon_div iF hU (iw _).gp (hom _) g hg.ax1 c1 hl hr _
    (fun l => (dAct k B w).mulVec fun i => algebraMap R k (u l i)) (fun l i => ⟨u l i, rfl⟩)
    (fun l i => ?_) N (fun l i => ?_) hβ m
  · rw [← hlin]
    exact lin_int (fun i => ⟨u l i, rfl⟩) ((iw w).int i)
  · rw [hlin, hN, Matrix.smul_mulVec]
    simp

end GlobalTheory
