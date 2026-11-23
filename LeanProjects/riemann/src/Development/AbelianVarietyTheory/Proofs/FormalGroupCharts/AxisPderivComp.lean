import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ChartChg
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.WickOperatorVanishing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GEWick
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GaugeTrans
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.NatCastMulCoeffOfPderivEq

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing

namespace GlobalTheory.ChartTrans

variable {k : Type} [CommRing k] {d : ℕ}

theorem pderiv_ev {m n : ℕ} (V : Fin m → Pt k n d) (hV : ∀ j, GP (V j)) (f : PS k m d)
    (v : Fin n × Fin d) :
    pderiv k v (ev V f) = ∑ j : Fin m, ∑ l : Fin d, ev V (pderiv k (j, l) f) * pderiv k v (V j l) := by
  unfold ev
  rw [GlobalTheory.FormalCalc.pderiv_subst (gt_hasSubst V hV), Fintype.sum_prod_type]

theorem ev_sum {m n : ℕ} (V : Fin m → Pt k n d) (hV : ∀ j, GP (V j)) {α : Type} (s : Finset α)
    (f : α → PS k m d) : ev V (∑ a ∈ s, f a) = ∑ a ∈ s, ev V (f a) :=
  GlobalTheory.FormalCalc.subst_sum' (gt_hasSubst V hV) s f

theorem ev_C {m n : ℕ} (V : Fin m → Pt k n d) (r : k) : ev V (C r : PS k m d) = C r := by
  unfold ev
  rw [MvPowerSeries.subst_C]

theorem ev_C_mul {m n : ℕ} (V : Fin m → Pt k n d) (hV : ∀ j, GP (V j)) (r : k) (f : PS k m d) :
    ev V (C r * f) = C r * ev V f := by
  rw [gt_ev_mul V hV, ev_C]

theorem vec1 {m n : ℕ} (V : Fin m → Pt k n d) (a : Pt k m d) :
    (fun j => evP V (![a] j)) = ![evP V a] := by
  funext j; fin_cases j; rfl

theorem ev_at_zero {n : ℕ} (f : PS k 1 d) : ev ![(0 : Pt k n d)] f = C (constantCoeff f) := by
  have e : f = C (constantCoeff f) + (f - C (constantCoeff f)) := by ring
  have h0 : constantCoeff (f - C (constantCoeff f)) = 0 := by simp
  conv_lhs => rw [e]
  rw [gt_ev_add _ (single_point_zero_constant gp_zero₂), ev_C]
  have h2 : ev ![(0 : Pt k n d)] (f - C (constantCoeff f)) = 0 := by
    change MvPowerSeries.subst (fun p : Fin 1 × Fin d => (![(0 : Pt k n d)] p.1) p.2) _ = 0
    have e : (fun p : Fin 1 × Fin d => (![(0 : Pt k n d)] p.1) p.2) = 0 := by
      funext p; simp
    rw [e]
    exact MvPowerSeries.subst_zero_of_constantCoeff_zero h0
  rw [h2, add_zero]

theorem axis_GP : ∀ j, GP ((![pt k (n := 1) d 0, 0] : Fin 2 → Pt k 1 d) j) :=
  pair_points_zero_constant (gp_pt 0) gp_zero₂

theorem dof_eq (F : Fin d → PS k 2 d) (hF : ∀ i, constantCoeff (F i) = 0)
    (hu : ∀ i, ev (n := 1) ![pt k (n := 1) d 0, 0] (F i) = (X ((0 : Fin 1), i) : PS k 1 d))
    (u : Fin d → k) (g : PS k 1 d) :
    Dof F u g = ∑ i, C (u i) *
      ev (n := 1) ![pt k (n := 1) d 0, 0] (pderiv k ((1 : Fin 2), i) (ev (n := 2) ![F] g)) := by
  have hF1 : ∀ j, GP ((![F] : Fin 1 → Pt k 2 d) j) := single_point_zero_constant hF
  have hS : ∀ h : PS k 1 d, ev (n := 1) ![pt k (n := 1) d 0, 0] (ev (n := 2) ![F] h) = h := by
    intro h
    rw [gt_ev_ev' _ _ axis_GP hF1, vec1]
    have : evP ![pt k (n := 1) d 0, 0] F = pt k (n := 1) d 0 := funext hu
    rw [this, gt_ev_pt_self]
  unfold Dof
  simp only [pderiv_ev _ hF1, Fin.sum_univ_one, ev_sum _ axis_GP, gt_ev_mul _ axis_GP, hS,
    Finset.mul_sum, Finset.sum_mul, Matrix.cons_val_zero]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem pderiv_comp_pt (φ : Pt k 1 d) (a b : Fin 2) (i l : Fin d) :
    pderiv k (a, i) (comp1 φ (pt k (n := 2) d b) l) =
      if a = b then ev ![pt k (n := 2) d b] (pderiv k ((0 : Fin 1), i) (φ l)) else 0 := by
  change pderiv k (a, i) (ev ![pt k (n := 2) d b] (φ l)) = _
  rw [pderiv_ev _ (single_point_zero_constant (gp_pt b)), Fin.sum_univ_one]
  simp only [Matrix.cons_val_zero, pt]
  split_ifs with h
  · subst h
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      rw [pderiv_X_of_ne (by simpa using hj), mul_zero]
    · simp
  · refine Finset.sum_eq_zero fun j _ => ?_
    rw [pderiv_X_of_ne (fun h' => h (congrArg Prod.fst h').symm), mul_zero]

theorem axis_pderiv_comp (φ : Pt k 1 d) (hφ : GP φ) (H : PS k 2 d) (i : Fin d) :
    ev (n := 1) ![pt k (n := 1) d 0, 0] (pderiv k ((1 : Fin 2), i)
      (ev ![comp1 φ (pt k (n := 2) d 0), comp1 φ (pt k (n := 2) d 1)] H)) =
    ∑ l, C (dLin φ l i) *
      ev ![φ] (ev (n := 1) ![pt k (n := 1) d 0, 0] (pderiv k ((1 : Fin 2), l) H)) := by
  have hΦ : ∀ j, GP (![comp1 φ (pt k (n := 2) d 0), comp1 φ (pt k (n := 2) d 1)] j) :=
    pair_points_zero_constant (gp_comp1 φ _ hφ (gp_pt 0)) (gp_comp1 φ _ hφ (gp_pt 1))
  have hK : ∀ K : PS k 2 d, ev (n := 1) ![pt k (n := 1) d 0, 0]
      (ev ![comp1 φ (pt k (n := 2) d 0), comp1 φ (pt k (n := 2) d 1)] K) =
      ev ![φ] (ev (n := 1) ![pt k (n := 1) d 0, 0] K) := by
    intro K
    rw [gt_ev_ev' _ _ axis_GP hΦ, eval_pair_points, evP_comp1 _ axis_GP φ _ (gp_pt 0),
      evP_comp1 _ axis_GP φ _ (gp_pt 1), evP_pt _ axis_GP, evP_pt _ axis_GP,
      gt_ev_ev' _ _ (single_point_zero_constant hφ) axis_GP, eval_pair_points, evP_pt _ (single_point_zero_constant hφ), evP_zero _ (single_point_zero_constant hφ)]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [gt_comp1_pt_right, gt_comp1_zero φ hφ]
  have hL : ∀ l, ev (n := 1) ![pt k (n := 1) d 0, 0]
      (ev ![pt k (n := 2) d 1] (pderiv k ((0 : Fin 1), i) (φ l))) = C (dLin φ l i) := by
    intro l
    rw [gt_ev_ev' _ _ axis_GP (single_point_zero_constant (gp_pt 1)), vec1, evP_pt _ axis_GP]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [ev_at_zero, ← coeff_zero_eq_constantCoeff_apply, coeff_pderiv]
    simp [dLin]
  rw [pderiv_ev _ hΦ, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, pderiv_comp_pt]
  simp only [one_ne_zero, if_false, if_true, mul_zero, Finset.sum_const_zero, zero_add]
  rw [ev_sum _ axis_GP]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [gt_ev_mul _ axis_GP, hK, hL, mul_comm]

theorem dof_transF (F : Fin d → PS k 2 d) (hF : ∀ i, constantCoeff (F i) = 0)
    (hu : ∀ i, ev (n := 1) ![pt k (n := 1) d 0, 0] (F i) = (X ((0 : Fin 1), i) : PS k 1 d))
    (φ φi : Pt k 1 d) (hinv : IsInvPair φ φi) (u : Fin d → k) (g : PS k 1 d) :
    Dof (transF F φ φi) u (ev (n := 1) ![φ] g) =
      ev (n := 1) ![φ] (Dof F ((dLin φ).mulVec u) g) := by
  have hφ : GP φ := hinv.1
  have hφi : GP φi := hinv.2.1
  have h0 : GP (comp1 φ (pt k (n := 2) d 0)) := gp_comp1 φ _ hφ (gp_pt 0)
  have h1 : GP (comp1 φ (pt k (n := 2) d 1)) := gp_comp1 φ _ hφ (gp_pt 1)
  have hΦ := pair_points_zero_constant h0 h1
  have hA := gp_addOf F hF _ _ h0 h1
  have eF : transF F φ φi =
      comp1 φi (addOf F (comp1 φ (pt k (n := 2) d 0)) (comp1 φ (pt k (n := 2) d 1))) := rfl
  have hF' : GP (transF F φ φi) := eF ▸ gp_comp1 φi _ hφi hA
  have hax : addOf F φ 0 = φ := by
    have e1 : addOf F (pt k (n := 1) d 0) 0 = pt k (n := 1) d 0 := funext hu
    have e2 := congrArg (evP ![φ]) e1
    rwa [evP_addOf _ (single_point_zero_constant hφ) _ _ _ (gp_pt 0) gp_zero₂, evP_pt _ (single_point_zero_constant hφ),
      evP_zero _ (single_point_zero_constant hφ)] at e2
  have hu' : evP ![pt k (n := 1) d 0, 0] (transF F φ φi) = pt k (n := 1) d 0 := by
    rw [eF, evP_comp1 _ axis_GP _ _ hA, evP_addOf _ axis_GP _ _ _ h0 h1,
      evP_comp1 _ axis_GP φ _ (gp_pt 0), evP_comp1 _ axis_GP φ _ (gp_pt 1),
      evP_pt _ axis_GP, evP_pt _ axis_GP]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [gt_comp1_pt_right, gt_comp1_zero φ hφ, hax, hinv.2.2.2]
  have key : ev (n := 2) ![transF F φ φi] (ev (n := 1) ![φ] g) =
      ev ![comp1 φ (pt k (n := 2) d 0), comp1 φ (pt k (n := 2) d 1)] (ev (n := 2) ![F] g) := by
    rw [gt_ev_ev' _ _ (single_point_zero_constant hF') (single_point_zero_constant hφ), vec1, gt_ev_ev' _ _ hΦ (single_point_zero_constant hF), vec1]
    have : evP ![transF F φ φi] φ = evP ![comp1 φ (pt k (n := 2) d 0), comp1 φ (pt k (n := 2) d 1)] F :=
      gt_comp_inv hinv _ hA
    rw [this]
  rw [dof_eq _ hF' (congrFun hu'), dof_eq F hF hu, key, ev_sum _ (single_point_zero_constant hφ)]
  simp only [axis_pderiv_comp φ hφ, ev_C_mul _ (single_point_zero_constant hφ)]
  simp only [Matrix.mulVec, dotProduct, map_sum,
    map_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem transPolySt : TransPolySt := by
  intro k _ d F hF hu φ φi hinv ι _ u P g
  have hφ : GP φ := hinv.1
  have hit : ∀ (v : Fin d → k) (n : ℕ) (g : PS k 1 d),
      (Dof (transF F φ φi) v)^[n] (ev (n := 1) ![φ] g) =
        ev (n := 1) ![φ] ((Dof F ((dLin φ).mulVec v))^[n] g) := by
    intro v n
    induction n with
    | zero => intro g; rfl
    | succ n ih =>
      intro g
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, dof_transF F hF hu φ φi hinv, ih]
  have hmon : ∀ m : ι →₀ ℕ, DmonOf (transF F φ φi) u m (ev (n := 1) ![φ] g) =
      ev (n := 1) ![φ] (DmonOf F (fun l => (dLin φ).mulVec (u l)) m g) := by
    intro m
    unfold DmonOf
    induction (Finset.univ : Finset ι).toList with
    | nil => rfl
    | cons a L ih => rw [List.foldr_cons, List.foldr_cons, ih, hit]
  unfold DpolyOf
  rw [ev_sum _ (single_point_zero_constant hφ)]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [ev_C_mul _ (single_point_zero_constant hφ), hmon]

end GlobalTheory.ChartTrans
