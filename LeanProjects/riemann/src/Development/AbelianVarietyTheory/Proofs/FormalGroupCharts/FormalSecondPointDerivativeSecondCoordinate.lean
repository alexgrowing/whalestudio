import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ChartChg
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.WickOperatorVanishing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GEWick
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GaugeTrans
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GaugeBilinearTermEqNegDoubleSum
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.DofDApply
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.NatCastMulCoeffOfPderivEq

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing

namespace GlobalTheory.QuadDeriv

variable {k : Type} [CommRing k] {d : ℕ}

theorem ev_sum {m n : ℕ} (V : Fin m → Pt k n d) (hV : ∀ j, GP (V j)) {α : Type} (s : Finset α)
    (f : α → PS k m d) : ev V (∑ a ∈ s, f a) = ∑ a ∈ s, ev V (f a) :=
  GlobalTheory.FormalCalc.subst_sum' (gt_hasSubst V hV) s f

theorem ev_C {m n : ℕ} (V : Fin m → Pt k n d) (r : k) : ev V (C r : PS k m d) = C r :=
  MvPowerSeries.subst_C r

theorem pderiv_ev {l m : ℕ} (a : Fin l → Pt k m d) (ha : ∀ j, GP (a j)) (f : PS k l d)
    (s : Fin m × Fin d) :
    pderiv k s (ev a f) = ∑ j, ∑ i, ev a (pderiv k (j, i) f) * pderiv k s (a j i) := by
  unfold ev
  rw [GlobalTheory.FormalCalc.pderiv_subst (gt_hasSubst a ha), Fintype.sum_prod_type]

theorem ev_pderiv_ev {l m n : ℕ} (V : Fin m → Pt k n d) (hV : ∀ j, GP (V j)) (a : Fin l → Pt k m d)
    (ha : ∀ j, GP (a j)) (f : PS k l d) (s : Fin m × Fin d) :
    ev V (pderiv k s (ev a f)) =
      ∑ j, ∑ i, ev (fun j => evP V (a j)) (pderiv k (j, i) f) * ev V (pderiv k s (a j i)) := by
  rw [pderiv_ev a ha, ev_sum V hV]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ev_sum V hV]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [gt_ev_mul V hV, gt_ev_ev' V a hV ha]

theorem vec1 {m n : ℕ} (V : Fin m → Pt k n d) (a : Pt k m d) :
    (fun j => evP V (![a] j)) = ![evP V a] := by
  funext j; fin_cases j; rfl

theorem pderiv_pt_ne {m : ℕ} {j j' : Fin m} (h : j' ≠ j) (i i' : Fin d) :
    pderiv k (j, i) (pt k d j' i') = 0 :=
  pderiv_X_of_ne fun e => h (congrArg Prod.fst e)

theorem pderiv_pt_self {m : ℕ} (j : Fin m) (i i' : Fin d) :
    pderiv k (j, i) (pt k d j i') = if i' = i then 1 else 0 := by
  split_ifs with h
  · subst h; exact pderiv_X_self
  · exact pderiv_X_of_ne fun e => h (congrArg Prod.snd e)

theorem pderiv_ev_eq_zero {l m : ℕ} (a : Fin l → Pt k m d) (ha : ∀ j, GP (a j)) (f : PS k l d)
    (s : Fin m × Fin d) (h : ∀ j i, pderiv k s (a j i) = 0) : pderiv k s (ev a f) = 0 := by
  rw [pderiv_ev a ha]
  simp [h]

theorem ev_zero_pts {l m : ℕ} (a : Fin l → Pt k m d) (ha : ∀ j, a j = 0) (f : PS k l d) :
    ev a f = C (constantCoeff f) := by
  have hG : ∀ j, GP (a j) := fun j => ha j ▸ gp_zero₂
  have e : f = C (constantCoeff f) + (f - C (constantCoeff f)) := by ring
  have h0 : constantCoeff (f - C (constantCoeff f)) = 0 := by simp
  conv_lhs => rw [e]
  rw [gt_ev_add a hG, ev_C]
  have e' : (fun p : Fin l × Fin d => a p.1 p.2) = 0 := by
    funext p; simp [ha]
  unfold ev
  rw [e', MvPowerSeries.subst_zero_of_constantCoeff_zero h0, add_zero]

theorem const_pderiv {σ : Type} (s : σ) (f : MvPowerSeries σ k) :
    constantCoeff (pderiv k s f) = coeff (Finsupp.single s 1) f := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_pderiv]
  simp

def dy (v : Fin d → k) (f : PS k 2 d) : PS k 1 d :=
  ∑ i, C (v i) * ev (n := 1) ![pt k d 0, 0] (pderiv k ((1 : Fin 2), i) f)

def lin (v : Fin d → k) (f : PS k 1 d) : k :=
  ∑ i, v i * constantCoeff (pderiv k ((0 : Fin 1), i) f)

theorem hX0 : ∀ j, GP ((![pt k d 0, 0] : Fin 2 → Pt k 1 d) j) := pair_points_zero_constant (gp_pt 0) gp_zero₂

theorem dy_add (v : Fin d → k) (f g : PS k 2 d) : dy v (f + g) = dy v f + dy v g := by
  simp only [dy, map_add, gt_ev_add _ hX0, mul_add, Finset.sum_add_distrib]

theorem dy_ev {l : ℕ} (v : Fin d → k) (a : Fin l → Pt k 2 d) (ha : ∀ j, GP (a j)) (f : PS k l d) :
    dy v (ev a f) = ∑ j, ∑ i, dy v (a j i) *
      ev (fun j => evP (n := 1) ![pt k d 0, 0] (a j)) (pderiv k (j, i) f) := by
  simp only [dy, ev_pderiv_ev _ hX0 a ha, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => by ring

theorem formalSecondPointDerivative_formalSubst_two (v : Fin d → k) (a b : Pt k 2 d) (ha : GP a) (hb : GP b) (f : PS k 2 d) :
    dy v (ev ![a, b] f) =
      ∑ i, dy v (a i) * ev ![evP (n := 1) ![pt k d 0, 0] a, evP (n := 1) ![pt k d 0, 0] b]
        (pderiv k ((0 : Fin 2), i) f) +
      ∑ i, dy v (b i) * ev ![evP (n := 1) ![pt k d 0, 0] a, evP (n := 1) ![pt k d 0, 0] b]
        (pderiv k ((1 : Fin 2), i) f) := by
  rw [dy_ev v _ (pair_points_zero_constant ha hb), Fin.sum_univ_two, eval_pair_points]
  rfl

theorem formalSecondPointDerivative_first_coordinate (v : Fin d → k) (i : Fin d) : dy v (pt k d 0 i) = 0 := by
  simp [dy, pderiv_pt_ne (show (0 : Fin 2) ≠ 1 by decide), gt_ev_zero _ hX0]

theorem formalSecondPointDerivative_second_coordinate (v : Fin d → k) (i : Fin d) : dy v (pt k d 1 i) = C (v i) := by
  simp only [dy, pderiv_pt_self]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    rw [if_neg (Ne.symm hb), gt_ev_zero _ hX0, mul_zero]
  · simp

theorem formalSecondPointDerivative_subst_first_point (v : Fin d → k) (f : PS k 1 d) : dy v (ev (n := 2) ![pt k d 0] f) = 0 := by
  rw [dy_ev v _ (single_point_zero_constant (gp_pt 0))]
  simp [formalSecondPointDerivative_first_coordinate]

theorem formalSecondPointDerivative_subst_second_point (v : Fin d → k) (f : PS k 1 d) :
    dy v (ev (n := 2) ![pt k d 1] f) = C (lin v f) := by
  rw [dy_ev v _ (single_point_zero_constant (gp_pt 1)), vec1, evP_pt _ hX0, lin, map_sum, Fin.sum_univ_one]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ev_zero_pts _ (by intro j; fin_cases j; rfl), map_mul]
  congr 1
  exact formalSecondPointDerivative_second_coordinate v i

theorem dof_eq (F : Fin d → PS k 2 d) (hF : GP F) (hU : evP (n := 1) ![pt k d 0, 0] F = pt k d 0)
    (v : Fin d → k) (f : PS k 1 d) : Dof F v f = dy v (ev ![F] f) := by
  rw [dy_ev v _ (single_point_zero_constant hF), vec1, hU, Fin.sum_univ_one]
  simp only [gt_ev_pt_self]
  rfl

theorem dof_additive (F : Fin d → PS k 2 d) (hF : GP F)
    (hU : evP (n := 1) ![pt k d 0, 0] F = pt k d 0) (v : Fin d → k) (f : PS k 1 d)
    (hf : ev ![F] f = ev (n := 2) ![pt k d 0] f + ev (n := 2) ![pt k d 1] f) :
    Dof F v f = C (lin v f) := by
  rw [dof_eq F hF hU, hf, dy_add, formalSecondPointDerivative_subst_first_point, formalSecondPointDerivative_subst_second_point, zero_add]

theorem addOf_pt (F : Fin d → PS k 2 d) : addOf F (pt k (n := 2) d 0) (pt k d 1) = F := by
  funext i
  change MvPowerSeries.subst (fun p : Fin 2 × Fin d => (![pt k (n := 2) d 0, pt k d 1] p.1) p.2) (F i) = F i
  have e : (fun p : Fin 2 × Fin d => (![pt k (n := 2) d 0, pt k d 1] p.1) p.2) = X := by
    funext p
    obtain ⟨j, i⟩ := p
    fin_cases j <;> rfl
  rw [e, MvPowerSeries.subst_self]
  rfl

section Biadd

variable (F : Fin d → PS k 2 d) (hF : GP F) (g : PS k 2 d)
include hF

theorem add_left
    (h : ev (n := 3) ![pt k d 0, pt k d 2] g + ev (n := 3) ![pt k d 1, pt k d 2] g =
      ev (n := 3) ![addOf F (pt k d 0) (pt k d 1), pt k d 2] g)
    {n : ℕ} (a b c : Pt k n d) (ha : GP a) (hb : GP b) (hc : GP c) :
    ev ![addOf F a b, c] g = ev ![a, c] g + ev ![b, c] g := by
  have hV := triple_points_zero_constant ha hb hc
  have hp : ∀ j : Fin 3, GP (pt k d j) := gp_pt
  have e := congrArg (ev ![a, b, c]) h
  rw [gt_ev_add _ hV, gt_ev_ev' _ _ hV (pair_points_zero_constant (hp _) (hp _)), gt_ev_ev' _ _ hV (pair_points_zero_constant (hp _) (hp _)),
    gt_ev_ev' _ _ hV (pair_points_zero_constant (gp_addOf F hF _ _ (hp _) (hp _)) (hp _)), eval_pair_points, eval_pair_points, eval_pair_points,
    evP_addOf _ hV F _ _ (hp _) (hp _)] at e
  simp only [evP_pt _ hV] at e
  exact e.symm

theorem add_right
    (h : ev (n := 3) ![pt k d 0, pt k d 1] g + ev (n := 3) ![pt k d 0, pt k d 2] g =
      ev (n := 3) ![pt k d 0, addOf F (pt k d 1) (pt k d 2)] g)
    {n : ℕ} (a b c : Pt k n d) (ha : GP a) (hb : GP b) (hc : GP c) :
    ev ![a, addOf F b c] g = ev ![a, b] g + ev ![a, c] g := by
  have hV := triple_points_zero_constant ha hb hc
  have hp : ∀ j : Fin 3, GP (pt k d j) := gp_pt
  have e := congrArg (ev ![a, b, c]) h
  rw [gt_ev_add _ hV, gt_ev_ev' _ _ hV (pair_points_zero_constant (hp _) (hp _)), gt_ev_ev' _ _ hV (pair_points_zero_constant (hp _) (hp _)),
    gt_ev_ev' _ _ hV (pair_points_zero_constant (hp _) (gp_addOf F hF _ _ (hp _) (hp _))), eval_pair_points, eval_pair_points, eval_pair_points,
    evP_addOf _ hV F _ _ (hp _) (hp _)] at e
  simp only [evP_pt _ hV] at e
  exact e.symm

end Biadd

def up (a : Pt k 2 d) : Pt k 3 d := evP (n := 3) ![pt k d 0, pt k d 1] a

theorem hUp : ∀ j, GP ((![pt k d 0, pt k d 1] : Fin 2 → Pt k 3 d) j) := pair_points_zero_constant (gp_pt 0) (gp_pt 1)

theorem hDown : ∀ j, GP ((![pt k d 0, pt k d 1, 0] : Fin 3 → Pt k 2 d) j) :=
  triple_points_zero_constant (gp_pt 0) (gp_pt 1) gp_zero₂

theorem constantCoeff_up_eq_zero₂ {a : Pt k 2 d} (ha : GP a) : GP (up a) := gp_evP _ hUp a ha

theorem down_up (a : Pt k 2 d) : evP (n := 2) ![pt k d 0, pt k d 1, 0] (up a) = a := by
  funext i
  change ev _ (ev _ (a i)) = _
  rw [gt_ev_ev' _ _ hDown hUp, eval_pair_points, evP_pt _ hDown, evP_pt _ hDown]
  exact congrFun (addOf_pt a) i

theorem pderiv_up (a : Pt k 2 d) (i i' : Fin d) : pderiv k ((2 : Fin 3), i) (up a i') = 0 := by
  refine pderiv_ev_eq_zero _ hUp _ _ fun j l => ?_
  fin_cases j
  · exact pderiv_pt_ne (show (0 : Fin 3) ≠ 2 by decide) _ _
  · exact pderiv_pt_ne (show (1 : Fin 3) ≠ 2 by decide) _ _

theorem sum_pt_self {m n : ℕ} (V : Fin m → Pt k n d) (hV : ∀ j, GP (V j)) (j : Fin m) (i : Fin d)
    (A : Fin d → PS k n d) : ∑ i', A i' * ev V (pderiv k (j, i) (pt k d j i')) = A i := by
  rw [Finset.sum_eq_single i]
  · simp [pderiv_pt_self]
  · intro b _ hb
    rw [pderiv_pt_self, if_neg hb, gt_ev_zero _ hV, mul_zero]
  · simp

theorem dz_right (g : PS k 2 d) (a : Pt k 2 d) (ha : GP a) (i : Fin d) :
    ev (n := 2) ![pt k d 0, pt k d 1, 0] (pderiv k ((2 : Fin 3), i) (ev ![up a, pt k d 2] g)) =
      ev ![a, 0] (pderiv k ((1 : Fin 2), i) g) := by
  rw [ev_pderiv_ev _ hDown _ (pair_points_zero_constant (constantCoeff_up_eq_zero₂ ha) (gp_pt 2)), Fin.sum_univ_two, eval_pair_points, down_up,
    evP_pt _ hDown]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, pderiv_up, gt_ev_zero _ hDown, mul_zero,
    Finset.sum_const_zero, zero_add]
  rw [sum_pt_self _ hDown]
  rfl

theorem dz_left (g : PS k 2 d) (a : Pt k 2 d) (ha : GP a) (i : Fin d) :
    ev (n := 2) ![pt k d 0, pt k d 1, 0] (pderiv k ((2 : Fin 3), i) (ev ![pt k d 2, up a] g)) =
      ev ![0, a] (pderiv k ((0 : Fin 2), i) g) := by
  rw [ev_pderiv_ev _ hDown _ (pair_points_zero_constant (gp_pt 2) (constantCoeff_up_eq_zero₂ ha)), Fin.sum_univ_two, eval_pair_points, down_up,
    evP_pt _ hDown]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, pderiv_up, gt_ev_zero _ hDown, mul_zero,
    Finset.sum_const_zero, add_zero]
  rw [sum_pt_self _ hDown]
  rfl

section Main

variable (F : Fin d → PS k 2 d) (hF : GP F) (g : PS k 2 d)
include hF

theorem dz_add_left
    (h : ev (n := 3) ![pt k d 0, pt k d 2] g + ev (n := 3) ![pt k d 1, pt k d 2] g =
      ev (n := 3) ![addOf F (pt k d 0) (pt k d 1), pt k d 2] g)
    (a b : Pt k 2 d) (ha : GP a) (hb : GP b) (i : Fin d) :
    ev ![addOf F a b, 0] (pderiv k ((1 : Fin 2), i) g) =
      ev ![a, 0] (pderiv k ((1 : Fin 2), i) g) + ev ![b, 0] (pderiv k ((1 : Fin 2), i) g) := by
  rw [← dz_right g _ (gp_addOf F hF _ _ ha hb), ← dz_right g _ ha, ← dz_right g _ hb,
    ← gt_ev_add _ hDown, ← map_add, ← add_left F hF g h _ _ _ (constantCoeff_up_eq_zero₂ ha) (constantCoeff_up_eq_zero₂ hb) (gp_pt 2)]
  unfold up
  rw [evP_addOf _ hUp F _ _ ha hb]

theorem dz_add_right
    (h : ev (n := 3) ![pt k d 0, pt k d 1] g + ev (n := 3) ![pt k d 0, pt k d 2] g =
      ev (n := 3) ![pt k d 0, addOf F (pt k d 1) (pt k d 2)] g)
    (a b : Pt k 2 d) (ha : GP a) (hb : GP b) (i : Fin d) :
    ev ![0, addOf F a b] (pderiv k ((0 : Fin 2), i) g) =
      ev ![0, a] (pderiv k ((0 : Fin 2), i) g) + ev ![0, b] (pderiv k ((0 : Fin 2), i) g) := by
  rw [← dz_left g _ (gp_addOf F hF _ _ ha hb), ← dz_left g _ ha, ← dz_left g _ hb,
    ← gt_ev_add _ hDown, ← map_add, ← add_right F hF g h _ _ _ (gp_pt 2) (constantCoeff_up_eq_zero₂ ha) (constantCoeff_up_eq_zero₂ hb)]
  unfold up
  rw [evP_addOf _ hUp F _ _ ha hb]

end Main

theorem formalSubst_single_of_formalSubst_two {n : ℕ} (a : Pt k n d) (ha : GP a) (b c : Pt k 1 d) (hb : GP b) (hc : GP c)
    (f : PS k 2 d) : ev ![a] (ev ![b, c] f) = ev ![comp1 b a, comp1 c a] f := by
  rw [gt_ev_ev' _ _ (single_point_zero_constant ha) (pair_points_zero_constant hb hc), eval_pair_points]
  rfl

theorem formalComp_zero_left_point {n : ℕ} (a : Pt k n d) (ha : GP a) : comp1 (0 : Pt k 1 d) a = 0 :=
  evP_zero _ (single_point_zero_constant ha)

theorem const_pderiv_pderiv (g : PS k 2 d) (i j : Fin d) :
    constantCoeff (pderiv k ((0 : Fin 2), i) (pderiv k ((1 : Fin 2), j) g)) =
      coeff (Finsupp.single ((0 : Fin 2), i) 1 + Finsupp.single ((1 : Fin 2), j) 1) g := by
  rw [const_pderiv, coeff_pderiv, Finsupp.single_eq_of_ne (by simp)]
  simp

theorem constantCoeff_pderiv_formalSubst_two (b c : Pt k 1 d) (hb : GP b) (hc : GP c) (f : PS k 2 d) (l : Fin d) :
    constantCoeff (pderiv k ((0 : Fin 1), l) (ev ![b, c] f)) =
      ∑ i, constantCoeff (pderiv k ((0 : Fin 2), i) f) * constantCoeff (pderiv k ((0 : Fin 1), l) (b i)) +
      ∑ i, constantCoeff (pderiv k ((1 : Fin 2), i) f) * constantCoeff (pderiv k ((0 : Fin 1), l) (c i)) := by
  rw [pderiv_ev _ (pair_points_zero_constant hb hc), Fin.sum_univ_two]
  simp only [map_add, map_sum, map_mul, gt_const_ev_eq _ (pair_points_zero_constant hb hc)]
  rfl

theorem quad (F : Fin d → PS k 2 d) (hF : GP F) (hU : evP (n := 1) ![pt k d 0, 0] F = pt k d 0)
    (w : Pt k 1 d) (hw : GP w)
    (hom : comp1 w F = addOf F (comp1 w (pt k (n := 2) d 0)) (comp1 w (pt k (n := 2) d 1)))
    (g : PS k 2 d) (h0 : ev (n := 1) ![0, pt k d 0] g = 0) (h1 : ev (n := 1) ![pt k d 0, 0] g = 0)
    (hl : ev (n := 3) ![pt k d 0, pt k d 2] g + ev (n := 3) ![pt k d 1, pt k d 2] g =
      ev (n := 3) ![addOf F (pt k d 0) (pt k d 1), pt k d 2] g)
    (hr : ev (n := 3) ![pt k d 0, pt k d 1] g + ev (n := 3) ![pt k d 0, pt k d 2] g =
      ev (n := 3) ![pt k d 0, addOf F (pt k d 1) (pt k d 2)] g) :
    constantCoeff (ev (n := 1) ![pt k d 0, w] g) = 0 ∧
    (∀ u, constantCoeff (Dof F u (ev (n := 1) ![pt k d 0, w] g)) = 0) ∧
    ∀ u v, Dof F u (Dof F v (ev (n := 1) ![pt k d 0, w] g)) =
      C (∑ j, (∑ l, v l * coeff (Finsupp.single ((0 : Fin 1), l) 1) (w j)) *
          (∑ i, u i * coeff (Finsupp.single ((0 : Fin 2), i) 1 + Finsupp.single ((1 : Fin 2), j) 1) g) +
        ∑ i, v i * ∑ l, u l * ∑ j,
          coeff (Finsupp.single ((0 : Fin 2), i) 1 + Finsupp.single ((1 : Fin 2), j) 1) g *
            coeff (Finsupp.single ((0 : Fin 1), l) 1) (w j)) := by
  have p0 : GP (pt k (n := 2) d 0) := gp_pt 0
  have p1 : GP (pt k (n := 2) d 1) := gp_pt 1
  have q0 : GP (pt k (n := 1) d 0) := gp_pt 0
  have w0 := gp_comp1 w _ hw p0
  have w1 := gp_comp1 w _ hw p1
  have c0 : constantCoeff g = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply]
    exact coeff_eq_zero_of_axes g h0 h1 0 (by simp)
  have c1 : ∀ s, constantCoeff (pderiv k s g) = 0 := fun s => by
    rw [const_pderiv]
    exact coeff_eq_zero_of_axes g h0 h1 _ (by simp)
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
  have hD : ∀ v, Dof F v (ev (n := 1) ![pt k d 0, w] g) =
      ∑ j, C (lin v (w j)) * ev (n := 1) ![pt k d 0, 0] (pderiv k ((1 : Fin 2), j) g) +
      ∑ i, C (v i) * ev (n := 1) ![0, w] (pderiv k ((0 : Fin 2), i) g) := by
    intro v
    rw [dof_eq F hF hU, formalSubst_single_of_formalSubst_two F hF _ _ q0 hw, gt_comp1_pt F hF, hom]
    have : ev ![F, addOf F (comp1 w (pt k (n := 2) d 0)) (comp1 w (pt k (n := 2) d 1))] g =
        ev ![addOf F (pt k d 0) (pt k d 1),
          addOf F (comp1 w (pt k (n := 2) d 0)) (comp1 w (pt k (n := 2) d 1))] g := by
      rw [addOf_pt]
    rw [this, add_left F hF g hl _ _ _ p0 p1 (gp_addOf F hF _ _ w0 w1),
      add_right F hF g hr _ _ _ p0 w0 w1, add_right F hF g hr _ _ _ p1 w0 w1,
      dy_add, dy_add, dy_add, formalSecondPointDerivative_formalSubst_two v _ _ p0 w0, formalSecondPointDerivative_formalSubst_two v _ _ p0 w1, formalSecondPointDerivative_formalSubst_two v _ _ p1 w0,
      formalSecondPointDerivative_formalSubst_two v _ _ p1 w1]
    simp only [e0, e1, f0, f1, g0, g1, formalSecondPointDerivative_first_coordinate, formalSecondPointDerivative_second_coordinate, z, zero_mul, mul_zero, Finset.sum_const_zero,
      zero_add, add_zero]
  refine ⟨by rw [gt_const_ev_eq _ (pair_points_zero_constant q0 hw), c0], fun u => ?_, fun u v => ?_⟩
  · rw [hD]
    simp only [map_add, map_sum, map_mul, gt_const_ev_eq _ hX0,
      gt_const_ev_eq _ (pair_points_zero_constant gp_zero₂ hw), c1, mul_zero, Finset.sum_const_zero, add_zero]
  · have hb : ∀ j, Dof F u (ev (n := 1) ![pt k d 0, 0] (pderiv k ((1 : Fin 2), j) g)) =
        C (∑ i, u i * coeff (Finsupp.single ((0 : Fin 2), i) 1 + Finsupp.single ((1 : Fin 2), j) 1) g) := by
      intro j
      rw [dof_additive F hF hU]
      · congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [constantCoeff_pderiv_formalSubst_two _ _ q0 gp_zero₂]
        simp [pderiv_pt_self, const_pderiv_pderiv, apply_ite]
      · rw [formalSubst_single_of_formalSubst_two _ hF _ _ q0 gp_zero₂, formalSubst_single_of_formalSubst_two _ p0 _ _ q0 gp_zero₂,
          formalSubst_single_of_formalSubst_two _ p1 _ _ q0 gp_zero₂, gt_comp1_pt _ hF, gt_comp1_pt _ p0, gt_comp1_pt _ p1,
          formalComp_zero_left_point _ hF, formalComp_zero_left_point _ p0, formalComp_zero_left_point _ p1,
          ← dz_add_left F hF g hl _ _ p0 p1, addOf_pt]
    have ha : ∀ i, Dof F u (ev (n := 1) ![0, w] (pderiv k ((0 : Fin 2), i) g)) =
        C (∑ l, u l * ∑ j,
          coeff (Finsupp.single ((0 : Fin 2), i) 1 + Finsupp.single ((1 : Fin 2), j) 1) g *
            coeff (Finsupp.single ((0 : Fin 1), l) 1) (w j)) := by
      intro i
      rw [dof_additive F hF hU]
      · congr 1
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [constantCoeff_pderiv_formalSubst_two _ _ gp_zero₂ hw]
        simp only [Pi.zero_apply, map_zero, mul_zero, Finset.sum_const_zero, zero_add]
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [GlobalTheory.FormalCalc.pderiv_comm, const_pderiv_pderiv, const_pderiv]
      · rw [formalSubst_single_of_formalSubst_two _ hF _ _ gp_zero₂ hw, formalSubst_single_of_formalSubst_two _ p0 _ _ gp_zero₂ hw,
          formalSubst_single_of_formalSubst_two _ p1 _ _ gp_zero₂ hw,
          formalComp_zero_left_point _ hF, formalComp_zero_left_point _ p0, formalComp_zero_left_point _ p1,
          ← dz_add_right F hF g hr _ _ w0 w1, hom]
    rw [hD, GE.dof_add, GE.dof_sum, GE.dof_sum]
    simp only [GE.dof_C_mul, ha, hb, ← map_mul, ← map_sum, ← map_add, lin, const_pderiv]

section BaseChange

variable {R : Type} [CommRing R] (φ : R →+* k)

theorem map_ev {m n : ℕ} (a : Fin m → Pt R n d) (ha : ∀ j, GP (a j)) (f : PS R m d) :
    MvPowerSeries.map φ (ev a f) =
      ev (fun j i => MvPowerSeries.map φ (a j i)) (MvPowerSeries.map φ f) := by
  unfold ev
  rw [MvPowerSeries.map_subst (gt_hasSubst a ha)]

def mapP {n : ℕ} (a : Pt R n d) : Pt k n d := fun i => MvPowerSeries.map φ (a i)

theorem baseChange_pt {n : ℕ} (j : Fin n) : mapP φ (pt R d j) = pt k d j := by
  funext i; simp [mapP, pt]

theorem baseChange_comp1 {n : ℕ} (w : Pt R 1 d) (a : Pt R n d) (ha : GP a) :
    mapP φ (comp1 w a) = comp1 (mapP φ w) (mapP φ a) := by
  funext i
  change MvPowerSeries.map φ (ev ![a] (w i)) = ev ![mapP φ a] _
  rw [map_ev φ _ (single_point_zero_constant ha)]
  congr 1
  funext j; fin_cases j; rfl

theorem baseChange_addOf {n : ℕ} (F : Pt R 2 d) (a b : Pt R n d) (ha : GP a) (hb : GP b) :
    mapP φ (addOf F a b) = addOf (mapP φ F) (mapP φ a) (mapP φ b) := by
  funext i
  change MvPowerSeries.map φ (ev ![a, b] (F i)) = ev ![mapP φ a, mapP φ b] _
  rw [map_ev φ _ (pair_points_zero_constant ha hb)]
  congr 1
  funext j; fin_cases j <;> rfl

theorem constantCoeff_mapP_eq_zero {n : ℕ} (a : Pt R n d) (ha : GP a) : GP (mapP φ a) := fun i => by
  simp [mapP, ha i]

theorem unit_right (G : FGLaw R d) : addOf G.F (pt R (n := 1) d 0) 0 = pt R d 0 := by
  funext i
  change ev ![pt R (n := 1) d 0, 0] (G.F i) = _
  rw [← G.comm i, gt_ev_ev' _ _ hX0 (pair_points_zero_constant (gp_pt 1) (gp_pt 0)), eval_pair_points, evP_pt _ hX0,
    evP_pt _ hX0]
  exact G.unit i

end BaseChange

end GlobalTheory.QuadDeriv

namespace GlobalTheory

open QuadDeriv

theorem quadDeriv_of_biadditive : G2.QuadraticFormDerivatives := by
  intro R _ d O _ _ k _ _ _ B g hg w0
  obtain ⟨h0, h1, hl, hr, -⟩ := hg
  have eF : B.FK k = mapP (algebraMap R k) B.G.F := rfl
  have ew : B.actK k w0 = mapP (algebraMap R k) (B.A.act w0) := rfl
  have hF : GP (B.FK k) := constantCoeff_mapP_eq_zero _ _ B.G.const
  have hw : GP (B.actK k w0) := constantCoeff_mapP_eq_zero _ _ (B.A.const w0)
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
  obtain ⟨a, b, c⟩ := quad (B.FK k) hF hU (B.actK k w0) hw hom g h0 h1 hl hr
  rw [gt_comp1_pt_right]
  refine ⟨a, b, fun u v => ?_⟩
  rw [c]
  congr 1
  simp only [dotProduct, Matrix.mulVec, bilinPart, dAct, Finset.mul_sum, Finset.sum_mul]
  congr 1
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun l _ => by ring
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring

end GlobalTheory
