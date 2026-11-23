import Formalism.LocalToGlobal.CharacterGerms.GermEvalOneStandardPointSelf
import Formalism.LocalToGlobal.CharacterGerms.MaximalOfValuationGeOne

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds.LiftedCoordinateEvaluation

open Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.PartialDerivEval Formalism.L2.FormalSeriesBounds.FirstUnitSeriesIntegrality Formalism.L2.FormalSeriesBounds.MulLFrob ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
  MvPowerSeries

variable {C : Type} [Field C] [CharZero C] {dd : ℕ}

abbrev P0 : Pt C 2 dd := pt C (n := 2) dd 0

abbrev P1 : Pt C 2 dd := pt C (n := 2) dd 1

theorem z0P0 : ∀ j, constantCoeff ((P0 : Pt C 2 dd) j) = 0 := fun j => z0_pt 0 j

theorem z0P1 : ∀ j, constantCoeff ((P1 : Pt C 2 dd) j) = 0 := fun j => z0_pt 1 j

theorem lift_eval_two_points {m : ℕ} {a : Fin m → Pt C 1 dd} (ha : Z0 a) (f : PS C m dd) :
    ev ![(P0 : Pt C 2 dd)] (ev a f) = ev (fun k j => ev ![(P0 : Pt C 2 dd)] (a k j)) f :=
  ev_ev ha (z0_1 _ z0P0) f

theorem eval_lifted_coordinate (j : Fin dd) : ev ![(P0 : Pt C 2 dd)] (pt C (n := 1) dd 0 j) = (P0 : Pt C 2 dd) j :=
  ev_X (z0_1 _ z0P0) 0 j

theorem lift_eval_zero (j : Fin dd) : ev ![(P0 : Pt C 2 dd)] ((0 : Pt C 1 dd) j) = 0 := by
  show ev ![(P0 : Pt C 2 dd)] (0 : PS C 1 dd) = 0
  exact ev_zero (z0_1 _ z0P0)

def J2 (G : FGLaw C dd) (k i : Fin dd) : PS C 2 dd := ev ![(P0 : Pt C 2 dd)] (JF G k i)

theorem group_law_jacobian_eq (G : FGLaw C dd) (k i : Fin dd) :
    J2 G k i = ev (n := 2) ![P0, 0] (pderiv C ((1 : Fin 2), i) (G.F k)) := by
  unfold J2 JF
  rw [lift_eval_two_points constant_zero_first_then_zero]
  congr 1
  funext k' j
  fin_cases k'
  · exact eval_lifted_coordinate j
  · exact lift_eval_zero j

theorem group_law_zero_two_points (G : FGLaw C dd) (k : Fin dd) : ev (n := 2) ![P0, 0] (G.F k) = (P0 : Pt C 2 dd) k := by
  have h := congrArg (ev ![(P0 : Pt C 2 dd)]) (formalGroupLaw_ev_x_zero G k)
  rw [lift_eval_two_points constant_zero_first_then_zero, ev_X (z0_1 _ z0P0) 0 k] at h
  rw [show (P0 : Pt C 2 dd) k = (![(P0 : Pt C 2 dd)] : Fin 1 → Pt C 2 dd) 0 k from rfl, ← h]
  congr 1
  funext k' j
  fin_cases k'
  · exact (eval_lifted_coordinate j).symm
  · exact (lift_eval_zero j).symm

def logJacobianTwoPoints {V : VF C} {O : Type} [CommRing O] [StarRing O] (Y : FBChart C V O dd) (k i : Fin dd) : PS C 2 dd :=
  ev ![(P0 : Pt C 2 dd)] (Jac Y.lg k i)

theorem jacobian_mul_log_jacobian {V : VF C} {O : Type} [CommRing O] [StarRing O] (Y : FBChart C V O dd) (k i : Fin dd) :
    ∑ m, J2 Y.B.G k m * logJacobianTwoPoints Y m i = if k = i then 1 else 0 := by
  have h1 : JF Y.B.G * Jac Y.lg = 1 := mul_eq_one_comm.1 (JL_JF Y)
  have h := congrFun (congrFun h1 k) i
  rw [Matrix.mul_apply, Matrix.one_apply] at h
  have h2 := congrArg (ev ![(P0 : Pt C 2 dd)]) h
  rw [ev_sum (z0_1 _ z0P0)] at h2
  simp only [ev_mul (z0_1 _ z0P0)] at h2
  unfold J2 logJacobianTwoPoints
  rw [h2]
  split_ifs
  · exact ev_one _
  · exact ev_zero (z0_1 _ z0P0)

variable {V : VF C} {O : Type} [CommRing O] [StarRing O]

def gk (Y : FBChart C V O dd) (k : Fin dd) : PS C 2 dd := pderiv C ((0 : Fin 2), k) Y.h

def Dh (Y : FBChart C V O dd) (m : Fin dd) : PS C 2 dd := ∑ k, gk Y k * J2 Y.B.G k m

def Az (Y : FBChart C V O dd) (m : Fin dd) : PS C 2 dd := ev (n := 2) ![0, P1] (gk Y m)

def Pm (Y : FBChart C V O dd) (m : Fin dd) : PS C 2 dd :=
  ev (n := 2) ![P0, 0, P1] (pderiv C ((1 : Fin 3), m) Y.B.ph1)

theorem constant_zero_point_third (P : Pt C 3 dd) (hP : ∀ j, constantCoeff (P j) = 0) :
    Z0 (![P, pt C (n := 3) dd 2] : Fin 2 → Pt C 3 dd) := fun k j => by
  fin_cases k
  · exact hP j
  · exact z0_pt 2 j

theorem constant_zero_lift_triple : Z0 (![P0, 0, P1] : Fin 3 → Pt C 2 dd) := fun k j => by
  fin_cases k
  · exact z0P0 j
  · exact map_zero _
  · exact z0P1 j

theorem pderiv_pt_ne {n : ℕ} (q : Fin n × Fin dd) (k : Fin n) (j : Fin dd) (h : k ≠ q.1) :
    pderiv C q (pt C dd k j) = 0 := by
  rw [pderiv_pt, if_neg (fun h' => h (congrArg Prod.fst h'))]

theorem pderiv_pt_same {n : ℕ} (k : Fin n) (j i : Fin dd) :
    pderiv C (k, i) (pt C dd k j) = if j = i then 1 else 0 := by
  rw [pderiv_pt]
  by_cases h : j = i
  · subst h; simp
  · rw [if_neg (fun h' => h (Prod.mk.inj h').2), if_neg h]

theorem dh_eq (Y : FBChart C V O dd) (m : Fin dd) : Dh Y m = Az Y m - Pm Y m := by
  have hph : Y.B.ph1 = FB.expS C (ev (n := 3) ![pt C dd 0, pt C dd 2] Y.h +
      ev (n := 3) ![pt C dd 1, pt C dd 2] Y.h -
      ev (n := 3) ![addOf Y.B.G.F (pt C dd 0) (pt C dd 1), pt C dd 2] Y.h) := by
    have := Y.gauge.ph1
    rwa [toK_self, FK_self] at this
  have hA : Z0 (![pt C (n := 3) dd 0, pt C dd 2] : Fin 2 → Pt C 3 dd) := z0_pp 0 2
  have hB : Z0 (![pt C (n := 3) dd 1, pt C dd 2] : Fin 2 → Pt C 3 dd) := z0_pp 1 2
  have hPP : Z0 (![pt C (n := 3) dd 0, pt C dd 1] : Fin 2 → Pt C 3 dd) := z0_pp 0 1
  have hadd : ∀ j, constantCoeff (addOf Y.B.G.F (pt C (n := 3) dd 0) (pt C dd 1) j) = 0 := fun j =>
    const_ev hPP (Y.B.G.const j)
  have hC : Z0 (![addOf Y.B.G.F (pt C (n := 3) dd 0) (pt C dd 1), pt C dd 2] : Fin 2 → Pt C 3 dd) :=
    constant_zero_point_third _ hadd
  have hE0 : constantCoeff (ev (n := 3) ![pt C dd 0, pt C dd 2] Y.h + ev (n := 3) ![pt C dd 1, pt C dd 2] Y.h -
      ev (n := 3) ![addOf Y.B.G.F (pt C dd 0) (pt C dd 1), pt C dd 2] Y.h) = 0 := by
    rw [map_sub, map_add, const_ev hA (h_const Y), const_ev hB (h_const Y), const_ev hC (h_const Y)]
    simp
  have dA : pderiv C ((1 : Fin 3), m) (ev (n := 3) ![pt C dd 0, pt C dd 2] Y.h) = 0 := by
    rw [pderiv_eval_pair hA]
    refine (congrArg₂ (· + ·) (Finset.sum_eq_zero fun j _ => ?_) (Finset.sum_eq_zero fun j _ => ?_)).trans
      (add_zero 0)
    · show _ * pderiv C _ (pt C (n := 3) dd 0 j) = 0
      rw [pderiv_pt_ne _ _ _ (by decide : (0 : Fin 3) ≠ 1), mul_zero]
    · show _ * pderiv C _ (pt C (n := 3) dd 2 j) = 0
      rw [pderiv_pt_ne _ _ _ (by decide : (2 : Fin 3) ≠ 1), mul_zero]
  have dB : pderiv C ((1 : Fin 3), m) (ev (n := 3) ![pt C dd 1, pt C dd 2] Y.h) =
      ev (n := 3) ![pt C dd 1, pt C dd 2] (gk Y m) := by
    rw [pderiv_eval_pair hB]
    refine (congrArg₂ (· + ·) ?_ (Finset.sum_eq_zero fun j _ => ?_)).trans (add_zero _)
    · rw [Finset.sum_eq_single m (fun j _ hj => by
          show _ * pderiv C _ (pt C (n := 3) dd 1 j) = 0
          rw [pderiv_pt_same, if_neg hj, mul_zero]) (fun h => absurd (Finset.mem_univ m) h)]
      show _ * pderiv C _ (pt C (n := 3) dd 1 m) = _
      rw [pderiv_pt_same, if_pos rfl, mul_one]
      rfl
    · show _ * pderiv C _ (pt C (n := 3) dd 2 j) = 0
      rw [pderiv_pt_ne _ _ _ (by decide : (2 : Fin 3) ≠ 1), mul_zero]
  have dQ : ∀ k, pderiv C ((1 : Fin 3), m) (addOf Y.B.G.F (pt C (n := 3) dd 0) (pt C dd 1) k) =
      ev (n := 3) ![pt C dd 0, pt C dd 1] (pderiv C ((1 : Fin 2), m) (Y.B.G.F k)) := by
    intro k
    show pderiv C ((1 : Fin 3), m) (ev (n := 3) ![pt C dd 0, pt C dd 1] (Y.B.G.F k)) = _
    rw [pderiv_eval_pair hPP]
    refine (congrArg₂ (· + ·) (Finset.sum_eq_zero fun j _ => ?_) ?_).trans (zero_add _)
    · show _ * pderiv C _ (pt C (n := 3) dd 0 j) = 0
      rw [pderiv_pt_ne _ _ _ (by decide : (0 : Fin 3) ≠ 1), mul_zero]
    · rw [Finset.sum_eq_single m (fun j _ hj => by
          show _ * pderiv C _ (pt C (n := 3) dd 1 j) = 0
          rw [pderiv_pt_same, if_neg hj, mul_zero]) (fun h => absurd (Finset.mem_univ m) h)]
      show _ * pderiv C _ (pt C (n := 3) dd 1 m) = _
      rw [pderiv_pt_same, if_pos rfl, mul_one]
  have dC : pderiv C ((1 : Fin 3), m) (ev (n := 3) ![addOf Y.B.G.F (pt C dd 0) (pt C dd 1), pt C dd 2] Y.h) =
      ∑ k, ev (n := 3) ![addOf Y.B.G.F (pt C dd 0) (pt C dd 1), pt C dd 2] (gk Y k) *
        ev (n := 3) ![pt C dd 0, pt C dd 1] (pderiv C ((1 : Fin 2), m) (Y.B.G.F k)) := by
    rw [pderiv_eval_pair hC]
    refine (congrArg₂ (· + ·) (Finset.sum_congr rfl fun k _ => ?_) (Finset.sum_eq_zero fun j _ => ?_)).trans
      (add_zero _)
    · show _ * pderiv C _ (addOf Y.B.G.F (pt C (n := 3) dd 0) (pt C dd 1) k) = _
      rw [dQ k]
      rfl
    · show _ * pderiv C _ (pt C (n := 3) dd 2 j) = 0
      rw [pderiv_pt_ne _ _ _ (by decide : (2 : Fin 3) ≠ 1), mul_zero]

  have hS := constant_zero_lift_triple (C := C) (dd := dd)
  have sB : ∀ f : PS C 2 dd, ev (n := 2) ![P0, 0, P1] (ev (n := 3) ![pt C dd 1, pt C dd 2] f) =
      ev (n := 2) ![0, P1] f := by
    intro f
    rw [ev_ev hB hS]
    congr 1
    funext k j
    fin_cases k
    · exact ev_X hS 1 j
    · exact ev_X hS 2 j
  have sP : ∀ f : PS C 2 dd, ev (n := 2) ![P0, 0, P1] (ev (n := 3) ![pt C dd 0, pt C dd 1] f) =
      ev (n := 2) ![P0, 0] f := by
    intro f
    rw [ev_ev hPP hS]
    congr 1
    funext k j
    fin_cases k
    · exact ev_X hS 0 j
    · exact ev_X hS 1 j
  have sC : ∀ f : PS C 2 dd, ev (n := 2) ![P0, 0, P1]
      (ev (n := 3) ![addOf Y.B.G.F (pt C dd 0) (pt C dd 1), pt C dd 2] f) = f := by
    intro f
    rw [ev_ev hC hS]
    have e : (fun k j => ev (n := 2) ![P0, 0, P1]
        ((![addOf Y.B.G.F (pt C (n := 3) dd 0) (pt C dd 1), pt C dd 2] : Fin 2 → Pt C 3 dd) k j)) =
        ![P0, P1] := by
      funext k j
      fin_cases k
      · show ev (n := 2) ![P0, 0, P1] (ev (n := 3) ![pt C dd 0, pt C dd 1] (Y.B.G.F j)) = (P0 : Pt C 2 dd) j
        rw [sP, group_law_zero_two_points]
      · exact ev_X hS 2 j
    rw [e]
    exact PartialDerivEval.eval_points_two f
  have hPm : Pm Y m = ev (n := 2) ![0, P1] (gk Y m) - ∑ k, gk Y k * J2 Y.B.G k m := by
    unfold Pm
    rw [hph, pderiv_expS hE0, ← hph, ev_mul hS, Y.B.cocycleLeft_zero_snd, one_mul, map_sub, map_add, dA, dB, dC, zero_add,
      ev_sub hS, sB, ev_sum hS]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [ev_mul hS, sC, sP, group_law_jacobian_eq]
  rw [hPm]
  unfold Dh Az
  ring

abbrev evl (Y : FBChart C V O dd) (n : ℕ) (f : PS C 2 dd) : PS C 2 dd := ev (n := 2) ![mm2 Y.B.G n, P1] f

theorem constant_zero_double_multiplication (Y : FBChart C V O dd) (n : ℕ) : Z0 (![mm2 Y.B.G n, P1] : Fin 2 → Pt C 2 dd) := constant_zero_double_multiplication_pair Y n

theorem eval_multiplication_jacobian (Y : FBChart C V O dd) (n : ℕ) (k m : Fin dd) :
    evl Y n (J2 Y.B.G k m) = ev ![mm2 Y.B.G n] (JF Y.B.G k m) := by
  unfold evl J2
  rw [ev_ev (z0_1 _ z0P0) (constant_zero_double_multiplication Y n)]
  congr 1
  funext k' j
  fin_cases k'
  exact ev_X (constant_zero_double_multiplication Y n) 0 j

theorem lift_eval_multiplication (Y : FBChart C V O dd) (n : ℕ) (f : PS C 1 dd) :
    ev ![(P0 : Pt C 2 dd)] (ev ![mulL Y.B.G.F n] f) = ev ![mm2 Y.B.G n] f := by
  rw [ev_ev (z0_1 _ (multiplication_constantCoeff_zero Y.B.G n)) (z0_1 _ z0P0)]
  congr 1
  funext k' j
  fin_cases k'
  rfl

theorem evl_Az (Y : FBChart C V O dd) (n : ℕ) (m : Fin dd) : evl Y n (Az Y m) = Az Y m := by
  unfold evl Az
  have h0 : Z0 (![(0 : Pt C 2 dd), P1] : Fin 2 → Pt C 2 dd) := fun k j => by
    fin_cases k
    · exact map_zero _
    · exact z0P1 j
  rw [ev_ev h0 (constant_zero_double_multiplication Y n)]
  congr 1
  funext k' j
  fin_cases k'
  · exact ev_zero (constant_zero_double_multiplication Y n)
  · exact ev_X (constant_zero_double_multiplication Y n) 1 j

theorem pderiv_double_multiplication_jacobian (Y : FBChart C V O dd) (n : ℕ) (k i : Fin dd) :
    pderiv C ((0 : Fin 2), i) (mm2 Y.B.G n k) = ev ![(P0 : Pt C 2 dd)] (Jac (mulL Y.B.G.F n) k i) := by
  show pderiv C ((0 : Fin 2), i) (ev ![(P0 : Pt C 2 dd)] (mulL Y.B.G.F n k)) = _
  rw [pderiv_eval_single (P := (P0 : Pt C 2 dd)) z0P0, Finset.sum_eq_single i (fun j _ hj => by
      show _ * pderiv C _ (pt C (n := 2) dd 0 j) = 0
      rw [pderiv_pt_same, if_neg hj, mul_zero]) (fun h => absurd (Finset.mem_univ i) h)]
  show _ * pderiv C _ (pt C (n := 2) dd 0 i) = _
  rw [pderiv_pt_same, if_pos rfl, mul_one]
  rfl

theorem pderiv_double_multiplication (Y : FBChart C V O dd) (n : ℕ) (k i : Fin dd) :
    pderiv C ((0 : Fin 2), i) (mm2 Y.B.G n k) = (n : PS C 2 dd) * ∑ m, evl Y n (J2 Y.B.G k m) * logJacobianTwoPoints Y m i := by
  rw [pderiv_double_multiplication_jacobian, jac_l, Matrix.smul_apply, Matrix.mul_apply, ev_eq_alg (z0_1 _ z0P0), map_nsmul,
    ← ev_eq_alg (z0_1 _ z0P0), ev_sum (z0_1 _ z0P0), nsmul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [ev_mul (z0_1 _ z0P0), eval_multiplication_jacobian]
  unfold MulLFrob.cmp logJacobianTwoPoints
  rw [lift_eval_multiplication]

theorem gk_eq (Y : FBChart C V O dd) (i : Fin dd) : gk Y i = ∑ m, Dh Y m * logJacobianTwoPoints Y m i := by
  unfold Dh
  simp only [Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, jacobian_mul_log_jacobian]
  rw [Finset.sum_eq_single i (fun k _ hk => by rw [if_neg hk, mul_zero]) (fun h => absurd (Finset.mem_univ i) h),
    if_pos rfl, mul_one]

theorem dE (Y : FBChart C V O dd) (i : Fin dd) :
    pderiv C ((0 : Fin 2), i) (evl Y V.l Y.h - (V.l : C) • Y.h) =
      (V.l : PS C 2 dd) * ∑ m, (Pm Y m - evl Y V.l (Pm Y m)) * logJacobianTwoPoints Y m i := by
  have h1 : pderiv C ((0 : Fin 2), i) (evl Y V.l Y.h) =
      (V.l : PS C 2 dd) * ∑ m, evl Y V.l (Dh Y m) * logJacobianTwoPoints Y m i := by
    unfold evl
    rw [pderiv_eval_pair (constant_zero_double_multiplication Y V.l)]
    rw [(Finset.sum_eq_zero fun k _ => by
        show _ * pderiv C _ (pt C (n := 2) dd 1 k) = 0
        rw [pderiv_pt_ne _ _ _ (by decide : (1 : Fin 2) ≠ 0), mul_zero] :
      ∑ k, ev (n := 2) ![mm2 Y.B.G V.l, P1] (pderiv C ((1 : Fin 2), k) Y.h) *
        pderiv C ((0 : Fin 2), i) ((![mm2 Y.B.G V.l, P1] : Fin 2 → Pt C 2 dd) 1 k) = 0), add_zero]
    have e : ∀ k, ev (n := 2) ![mm2 Y.B.G V.l, P1] (pderiv C ((0 : Fin 2), k) Y.h) *
        pderiv C ((0 : Fin 2), i) ((![mm2 Y.B.G V.l, P1] : Fin 2 → Pt C 2 dd) 0 k) =
        (V.l : PS C 2 dd) * ∑ m, evl Y V.l (gk Y k) * evl Y V.l (J2 Y.B.G k m) * logJacobianTwoPoints Y m i := by
      intro k
      show _ * pderiv C ((0 : Fin 2), i) (mm2 Y.B.G V.l k) = _
      rw [pderiv_double_multiplication, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      unfold gk evl
      ring
    rw [Finset.sum_congr rfl fun k _ => e k, ← Finset.mul_sum, Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun m _ => ?_
    unfold Dh evl
    rw [ev_sum (constant_zero_double_multiplication Y V.l), Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [ev_mul (constant_zero_double_multiplication Y V.l)]
  have h2 : pderiv C ((0 : Fin 2), i) ((V.l : C) • Y.h) = (V.l : PS C 2 dd) * ∑ m, Dh Y m * logJacobianTwoPoints Y m i := by
    rw [Nat.cast_smul_eq_nsmul, map_nsmul, nsmul_eq_mul, ← gk_eq]
    rfl
  rw [map_sub, h1, h2, ← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← sub_mul, dh_eq, evl, ev_sub (constant_zero_double_multiplication Y V.l), ← evl, ← evl, evl_Az]
  ring

end Formalism.L2.FormalSeriesBounds.LiftedCoordinateEvaluation

namespace Formalism.L2.FormalSeriesBounds

open LiftedCoordinateEvaluation MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem first_unit_series_frobenius : FirstUnitSeriesFrobenius := by
  intro C _ _ V O _ _ dd Y μ hμ
  obtain ⟨i, hi⟩ := hμ
  have hu : Y.u1 = FB.expS C (evl Y V.l Y.h - (V.l : C) • Y.h) := rfl
  have hE0 : constantCoeff (evl Y V.l Y.h - (V.l : C) • Y.h) = 0 := by
    rw [map_sub, show (V.l : C) • Y.h = ((V.l : ℕ) : PS C 2 dd) * Y.h by
      rw [Nat.cast_smul_eq_nsmul, nsmul_eq_mul], map_mul, PartialDerivEval.h_const, mul_zero, sub_zero]
    exact FirstUnitSeriesIntegrality.height_multiple_constantCoeff Y V.l
  have hd : pderiv C ((0 : Fin 2), i) Y.u1 =
      (V.l : PS C 2 dd) * (Y.u1 * ∑ m, (Pm Y m - evl Y V.l (Pm Y m)) * logJacobianTwoPoints Y m i) := by
    rw [hu, PartialDerivEval.pderiv_expS hE0, dE, ← hu]; ring
  have hint : IntS V (Y.u1 * ∑ m, (Pm Y m - evl Y V.l (Pm Y m)) * logJacobianTwoPoints Y m i) := by
    refine PartialDerivEval.intS_mul (first_unit_series_integral C V O dd Y)
      (PartialDerivEval.intS_sum _ fun m _ => PartialDerivEval.intS_mul ?_ ?_)
    · have hP : IntS V (Pm Y m) := by
        refine PartialDerivEval.intS_ev constant_zero_lift_triple (fun k j => ?_) (PartialDerivEval.intS_pderiv Y.intPh1 _)
        fin_cases k
        · exact PartialDerivEval.intS_X _
        · exact PartialDerivEval.intS_zero
        · exact PartialDerivEval.intS_X _
      have hP' : IntS V (evl Y V.l (Pm Y m)) := by
        refine PartialDerivEval.intS_ev (constant_zero_double_multiplication Y V.l) (fun k j => ?_) hP
        fin_cases k
        · exact FirstUnitSeriesIntegrality.double_multiplication_integral Y.B.G Y.intF V.l j
        · exact PartialDerivEval.intS_X _
      rw [sub_eq_add_neg]
      exact PartialDerivEval.intS_add hP (PartialDerivEval.intS_neg hP')
    · refine PartialDerivEval.intS_ev (PartialDerivEval.z0_1 _ z0P0) (fun k j => ?_) (MulLFrob.JL_int Y m i)
      fin_cases k
      exact PartialDerivEval.intS_X _
  have hmms : MaximalIdealCongruence.MMS V (pderiv C ((0 : Fin 2), i) Y.u1) := by
    rw [hd]; exact MaximalIdealCongruence.mms_l_mul hint
  have hm0 : μ ((0 : Fin 2), i) ≠ 0 := fun h => hi (h ▸ dvd_zero _)
  set ν := μ - Finsupp.single ((0 : Fin 2), i) 1 with hν
  have hνμ : ν + Finsupp.single ((0 : Fin 2), i) 1 = μ := by
    rw [hν]; refine tsub_add_cancel_of_le ?_
    rw [Finsupp.single_le_iff]; omega
  have hνi : ν ((0 : Fin 2), i) + 1 = μ ((0 : Fin 2), i) := by
    rw [← hνμ, Finsupp.add_apply, Finsupp.single_eq_same]
  have hc := hmms ν
  rw [coeff_pderiv, hνμ] at hc
  have hmC : ((ν ((0 : Fin 2), i) : C) + 1) = ((μ ((0 : Fin 2), i) : ℕ) : C) := by
    rw [← hνi]; push_cast; ring
  rw [hmC, mul_comm] at hc
  exact MaximalIdealCongruence.mm_of_natCast_mul hi (first_unit_series_integral C V O dd Y μ) hc

end Formalism.L2.FormalSeriesBounds
