import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ConnectionKillsSeries
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FormalSecondPointDerivativeSecondCoordinate
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FormalExpMulFormalExpNeg
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IntAASubstOfHasSubst

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing

namespace GlobalTheory.SigmaDefect

open GlobalTheory.QuadDeriv GlobalTheory.IntSeries

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
  {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k]

omit [Algebra ℚ k] in
theorem ev_sgOf (h : PS k 2 d) (i : Fin d) {n : ℕ} (a : Pt k n d) (ha : GP a) :
    ev ![a] (sgOf k h i) = -ev ![a, 0] (pderiv k ((1 : Fin 2), i) h) := by
  have h1 : ∀ j, GP ((![a] : Fin 1 → Pt k n d) j) := single_point_zero_constant ha
  have e : sgOf k h i = 0 - ev (n := 1) ![pt k d 0, 0] (pderiv k ((1 : Fin 2), i) h) := by
    rw [zero_sub]; rfl
  have z : evP ![a] (0 : Pt k 1 d) = 0 := funext fun _ => gt_ev_zero _ h1
  rw [e, gt_ev_sub _ h1, gt_ev_zero _ h1, zero_sub, gt_ev_ev' _ _ h1 hX0, eval_pair_points,
    evP_pt _ h1, z]
  rfl

omit [Algebra ℚ k] in
theorem GP_FK (B : FB R d O) : GP (B.FK k) := constantCoeff_mapP_eq_zero _ _ B.G.const

omit [Algebra ℚ k] in
theorem FK_unit_right (B : FB R d O) : evP (n := 1) ![pt k d 0, 0] (B.FK k) = pt k d 0 := by
  have := congrArg (mapP (algebraMap R k)) (unit_right B.G)
  rw [baseChange_addOf _ _ _ _ (gp_pt 0) gp_zero₂, baseChange_pt,
    show mapP (algebraMap R k) (0 : Pt R 1 d) = 0 from funext fun i => map_zero _] at this
  exact this

omit [Algebra ℚ k] in
theorem sigma_defect_eval_phase_one (B : FB R d O) :
    ev (n := 2) ![pt k d 0, pt k d 1, 0] (FB.toK k B.ph1) = 1 := by
  have := congrArg (MvPowerSeries.map (algebraMap R k)) B.cocycleLeft_zero_thd
  rw [map_ev _ _ hDown, map_one] at this
  rw [← this]
  congr 1
  funext j i
  fin_cases j <;> simp [pt]

theorem sgOf_defect (B : FB R d O) (h : PS k 2 d) (hc : B.IsCanonGauge k h) (i : Fin d) :
    ev ![B.FK k] (sgOf k h i) = ev (n := 2) ![pt k d 0] (sgOf k h i) +
      ev (n := 2) ![pt k d 1] (sgOf k h i) +
      ev (n := 2) ![pt k d 0, pt k d 1, 0] (pderiv k ((2 : Fin 3), i) (FB.toK k B.ph1)) := by
  have hF := GP_FK (k := k) B
  have hp : ∀ j : Fin 2, GP (pt k d j) := gp_pt
  have h0 : constantCoeff h = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply]
    exact coeff_eq_zero_of_vanish_first_axis h hc.ax0 0 fun _ => rfl
  have u0 : (pt k d 0 : Pt k 3 d) = up (pt k d 0) := (evP_pt _ (hUp (k := k) (d := d)) 0).symm
  have u1 : (pt k d 1 : Pt k 3 d) = up (pt k d 1) := (evP_pt _ (hUp (k := k) (d := d)) 1).symm
  have uF : addOf (B.FK k) (pt k d 0 : Pt k 3 d) (pt k d 1) = up (B.FK k) := rfl
  have hE : FB.toK k B.ph1 = GlobalTheory.FormalCalc.formalExp (ev ![up (pt k d 0), pt k d 2] h +
      ev ![up (pt k d 1), pt k d 2] h - ev ![up (B.FK k), pt k d 2] h) := by
    rw [← u0, ← u1, ← uF]; exact hc.ph1
  have c : ∀ a : Pt k 2 d, GP a → constantCoeff (ev ![up a, pt k d 2] h) = 0 := fun a ha =>
    gt_const_ev _ (pair_points_zero_constant (constantCoeff_up_eq_zero₂ ha) (gp_pt 2)) h h0
  have hD := GlobalTheory.FormalCalc.pderiv_formalExp (f := ev ![up (pt k d 0), pt k d 2] h +
      ev ![up (pt k d 1), pt k d 2] h - ev ![up (B.FK k), pt k d 2] h)
    (by rw [map_sub, map_add, c _ (hp 0), c _ (hp 1), c _ hF]; simp) ((2 : Fin 3), i)
  rw [← hE] at hD
  rw [hD, gt_ev_mul _ hDown, sigma_defect_eval_phase_one, one_mul, map_sub, map_add, gt_ev_sub _ hDown,
    gt_ev_add _ hDown, dz_right _ _ (hp 0), dz_right _ _ (hp 1), dz_right _ _ hF,
    ev_sgOf _ _ _ hF, ev_sgOf _ _ _ (hp 0), ev_sgOf _ _ _ (hp 1)]
  ring

omit [Algebra ℚ k] in
theorem intAA_ev {m n : ℕ} (a : Fin m → Pt k n d) (ha : ∀ j, GP (a j))
    (hai : ∀ j i, IntAA (R := R) k (a j i)) {f : PS k m d} (hf : IntAA (R := R) k f) :
    IntAA (R := R) k (ev a f) :=
  intAA_subst (fun p => ha p.1 p.2) (fun p => hai p.1 p.2) hf

theorem main : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h : PS k 2 d), B.IsCanonGauge k h → ∀ (u : Fin d → R) (i : Fin d), IntAA (R := R) k (Dof (B.FK k) (fun j => algebraMap R k (u j)) (sgOf k h i) - C ((sg1 k h).mulVec (fun j => algebraMap R k (u j)) i)) := by
  intro R _ d O _ _ k _ _ _ B h hc u i
  have hl : lin (fun j => algebraMap R k (u j)) (sgOf k h i) =
      (sg1 k h).mulVec (fun j => algebraMap R k (u j)) i := by
    simp only [lin, const_pderiv, Matrix.mulVec, dotProduct, sg1, mul_comm]
  rw [dof_eq _ (GP_FK B) (FK_unit_right B), sgOf_defect B h hc, dy_add, dy_add, formalSecondPointDerivative_subst_first_point,
    formalSecondPointDerivative_subst_second_point, hl, zero_add, add_sub_cancel_left]
  refine intAA_sum _ fun j _ => intAA_mul (intAA_C _) (intAA_ev _ hX0 ?_ (intAA_pderiv _
    (intAA_ev _ hDown ?_ (intAA_pderiv _ (intAA_map _)))))
  · intro l s
    fin_cases l
    exacts [intAA_X _, intAA_zero]
  · intro l s
    fin_cases l
    exacts [intAA_X _, intAA_X _, intAA_zero]

end GlobalTheory.SigmaDefect
