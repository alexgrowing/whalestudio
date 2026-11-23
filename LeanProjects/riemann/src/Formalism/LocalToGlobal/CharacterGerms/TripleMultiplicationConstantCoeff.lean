import Formalism.LocalToGlobal.CharacterGerms.IndexRaiseFirst

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds.FunEq

open Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.PartialDerivEval Formalism.L2.FormalSeriesBounds.FirstUnitSeriesIntegrality Formalism.L2.FormalSeriesBounds.MulLFrob ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
  MvPowerSeries

variable {C : Type} [Field C] [CharZero C] {dd : ℕ} {V : VF C} {O : Type} [CommRing O] [StarRing O]

abbrev p3 (k : Fin 3) : Pt C 3 dd := pt C (n := 3) dd k

theorem z0p3 (k : Fin 3) : ∀ j, constantCoeff ((p3 k : Pt C 3 dd) j) = 0 := by
  intro j
  simp [p3, pt]

theorem pderiv_eval_triple {n : ℕ} {a : Fin 3 → Pt C n dd} (ha : Z0 a) (f : PS C 3 dd) (q : Fin n × Fin dd) :
    pderiv C q (ev a f) = ∑ j, ev a (pderiv C ((0 : Fin 3), j) f) * pderiv C q (a 0 j) +
      ∑ j, ev a (pderiv C ((1 : Fin 3), j) f) * pderiv C q (a 1 j) +
      ∑ j, ev a (pderiv C ((2 : Fin 3), j) f) * pderiv C q (a 2 j) := by
  unfold ev
  rw [Formalism.G.LogCR.pderiv_subst (a := fun p : Fin 3 × Fin dd => a p.1 p.2) (fun p => ha p.1 p.2) f q,
    Fintype.sum_prod_type, Fin.sum_univ_three]

theorem d_ev_keep {f : PS C 2 dd} {B : Pt C 3 dd} (hB : ∀ j, constantCoeff (B j) = 0) (i : Fin dd)
    (hd : ∀ j, pderiv C ((0 : Fin 3), i) (B j) = 0) :
    pderiv C ((0 : Fin 3), i) (ev (n := 3) ![p3 0, B] f) = ev (n := 3) ![p3 0, B] (pderiv C ((0 : Fin 2), i) f) := by
  have hz : Z0 (![p3 0, B] : Fin 2 → Pt C 3 dd) := fun k j => by
    fin_cases k
    · exact z0p3 0 j
    · exact hB j
  rw [pderiv_eval_pair hz]
  refine (congrArg₂ (· + ·) ?_ (Finset.sum_eq_zero fun j _ => ?_)).trans (add_zero _)
  · rw [Finset.sum_eq_single i (fun j _ hj => by
        show _ * pderiv C _ (pt C (n := 3) dd 0 j) = 0
        rw [LiftedCoordinateEvaluation.pderiv_pt_same, if_neg hj, mul_zero]) (fun h => absurd (Finset.mem_univ i) h)]
    show _ * pderiv C _ (pt C (n := 3) dd 0 i) = _
    rw [LiftedCoordinateEvaluation.pderiv_pt_same, if_pos rfl, mul_one]
  · show _ * pderiv C _ (B j) = 0
    rw [hd j, mul_zero]

theorem d_ev_keep_iter {f : PS C 2 dd} {B : Pt C 3 dd} (hB : ∀ j, constantCoeff (B j) = 0) (i : Fin dd)
    (hd : ∀ j, pderiv C ((0 : Fin 3), i) (B j) = 0) (L : ℕ) :
    (pderiv C ((0 : Fin 3), i))^[L] (ev (n := 3) ![p3 0, B] f) =
      ev (n := 3) ![p3 0, B] ((pderiv C ((0 : Fin 2), i))^[L] f) := by
  induction L with
  | zero => rfl
  | succ L ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, d_ev_keep hB i hd]

def SS (G : FGLaw C dd) : Pt C 3 dd := addOf G.F (p3 1) (p3 2)

theorem triple_sum_constantCoeff (G : FGLaw C dd) (j : Fin dd) : constantCoeff (SS G j) = 0 :=
  const_ev (z0_pp 1 2) (G.const j)

theorem SS_int (G : FGLaw C dd) (hF : ∀ i, IntS V (G.F i)) (j : Fin dd) : IntS V (SS G j) :=
  intS_ev (z0_pp 1 2) (fun k m => by fin_cases k <;> exact intS_X _) (hF j)

theorem SS_d (G : FGLaw C dd) (i j : Fin dd) : pderiv C ((0 : Fin 3), i) (SS G j) = 0 := by
  show pderiv C ((0 : Fin 3), i) (ev (n := 3) ![p3 1, p3 2] (G.F j)) = 0
  rw [pderiv_eval_pair (z0_pp 1 2)]
  refine (congrArg₂ (· + ·) (Finset.sum_eq_zero fun m _ => ?_) (Finset.sum_eq_zero fun m _ => ?_)).trans
    (add_zero 0)
  · show _ * pderiv C _ (pt C (n := 3) dd 1 m) = 0
    rw [LiftedCoordinateEvaluation.pderiv_pt_ne _ _ _ (by decide : (1 : Fin 3) ≠ 0), mul_zero]
  · show _ * pderiv C _ (pt C (n := 3) dd 2 m) = 0
    rw [LiftedCoordinateEvaluation.pderiv_pt_ne _ _ _ (by decide : (2 : Fin 3) ≠ 0), mul_zero]

theorem triple_point_pderiv_first_zero (k : Fin 3) (hk : k ≠ 0) (i j : Fin dd) : pderiv C ((0 : Fin 3), i) ((p3 k : Pt C 3 dd) j) = 0 := by
  simp [p3, pt, MvPowerSeries.pderiv_X, Pi.single_apply, Prod.ext_iff, Ne.symm hk]

def m3 (G : FGLaw C dd) (n : ℕ) : Pt C 3 dd := fun k => ev ![(p3 0 : Pt C 3 dd)] (mulL G.F n k)

theorem triple_multiplication_constantCoeff (G : FGLaw C dd) (n : ℕ) (k : Fin dd) : constantCoeff (m3 G n k) = 0 :=
  const_ev (z0_1 _ (z0p3 0)) (multiplication_constantCoeff_zero G n k)

theorem triple_multiplication_integral (G : FGLaw C dd) (hF : ∀ i, IntS V (G.F i)) (n : ℕ) (k : Fin dd) : IntS V (m3 G n k) :=
  intS_ev (z0_1 _ (z0p3 0)) (fun k' m => by fin_cases k'; exact intS_X _) (mulL_int G hF n k)

def UU (Y : FBChart C V O dd) (w : Pt C 3 dd) : PS C 3 dd := ev (n := 3) ![p3 0, w] Y.u1

def QQ (Y : FBChart C V O dd) : PS C 3 dd := ev (n := 3) ![m3 Y.B.G V.l, p3 1, p3 2] Y.B.ph2

theorem ex_nsmul {σ : Type} (f : MvPowerSeries σ C) (hf : constantCoeff f = 0) (n : ℕ) :
    ex (n • f) = ex f ^ n := by
  induction n with
  | zero => simp [ex_zero]
  | succ n ih =>
    rw [succ_nsmul, ex_add _ _ (by simp [hf]) hf, ih, pow_succ]

theorem height_at_zero_first (Y : FBChart C V O dd) {n : ℕ} (W : Pt C n dd) (hW : ∀ j, constantCoeff (W j) = 0) :
    ev (n := n) ![0, W] Y.h = 0 := by
  have h0 := Y.gauge.ax0
  have hz : Z0 (![(0 : Pt C 1 dd), pt C (n := 1) dd 0] : Fin 2 → Pt C 1 dd) := fun k j => by
    fin_cases k
    · exact map_zero _
    · exact z0_pt 0 j
  have h1 := congrArg (ev ![W]) h0
  rw [ev_ev hz (z0_1 W hW), ev_zero (z0_1 W hW)] at h1
  rw [← h1]
  congr 1
  funext k j
  fin_cases k
  · exact (ev_zero (z0_1 W hW)).symm
  · exact (ev_X (z0_1 W hW) 0 j).symm

theorem restrict_triple_multiplication (G : FGLaw C dd) (n : ℕ) (j : Fin dd) : ev (rz 2) (m3 G n j) = 0 := by
  unfold m3
  rw [ev_ev (z0_1 _ (z0p3 0)) (constant_zero_restrict_points 2)]
  have e : (fun k m => ev (rz (C := C) (dd := dd) 2) ((![(p3 0 : Pt C 3 dd)] : Fin 1 → Pt C 3 dd) k m)) =
      ![(0 : Pt C 2 dd)] := by
    funext k m
    fin_cases k
    exact ev_X (constant_zero_restrict_points 2) 0 m
  rw [e, ev_zero_pt, multiplication_constantCoeff_zero, map_zero]

theorem constant_zero_two_points {w : Pt C 3 dd} (P : Pt C 3 dd) (hP : ∀ j, constantCoeff (P j) = 0)
    (hw : ∀ j, constantCoeff (w j) = 0) : Z0 (![P, w] : Fin 2 → Pt C 3 dd) := by
  intro i j
  fin_cases i
  · exact hP j
  · exact hw j

theorem ev_smulC {m n : ℕ} {a : Fin m → Pt C n dd} (ha : Z0 a) (c : C) (f : PS C m dd) :
    ev a (c • f) = c • ev a f := by
  rw [ev_eq_alg ha, map_smul, ← ev_eq_alg ha]

theorem UU_eq (Y : FBChart C V O dd) (w : Pt C 3 dd) (hw : ∀ j, constantCoeff (w j) = 0) :
    UU Y w = ex (ev (n := 3) ![m3 Y.B.G V.l, w] Y.h - (V.l : C) • ev (n := 3) ![p3 0, w] Y.h) := by
  have hz := constant_zero_two_points (p3 0) (z0p3 0) hw
  have hE0 : constantCoeff (gg Y V.l - (V.l : C) • Y.h) = 0 := by
    rw [map_sub, show (V.l : C) • Y.h = ((V.l : ℕ) : PS C 2 dd) * Y.h by
      rw [Nat.cast_smul_eq_nsmul, nsmul_eq_mul], map_mul, h_const, mul_zero, sub_zero]
    exact height_multiple_constantCoeff Y V.l
  unfold UU
  rw [show Y.u1 = ex (gg Y V.l - (V.l : C) • Y.h) from rfl, ev_ex hz _ hE0, ev_sub hz, ev_smulC hz]
  congr 2
  unfold gg
  rw [ev_ev (constant_zero_double_multiplication_pair Y V.l) hz]
  congr 1
  funext k j
  fin_cases k
  · show ev ![p3 0, w] (ev ![pt C (n := 2) dd 0] (mulL Y.B.G.F V.l j)) = m3 Y.B.G V.l j
    rw [ev_ev (z0_1 _ (fun j => z0_pt 0 j)) hz]
    congr 1
    funext k' m
    fin_cases k'
    exact ev_X hz 0 m
  · exact ev_X hz 1 j

theorem hph2 (Y : FBChart C V O dd) : Y.B.ph2 = ex (ev (n := 3) ![p3 0, p3 1] Y.h + ev (n := 3) ![p3 0, p3 2] Y.h -
    ev (n := 3) ![p3 0, SS Y.B.G] Y.h) := by
  have := Y.gauge.ph2
  rwa [toK_self, FK_self] at this

theorem eval_height_constantCoeff (Y : FBChart C V O dd) {P w : Pt C 3 dd} (hP : ∀ j, constantCoeff (P j) = 0)
    (hw : ∀ j, constantCoeff (w j) = 0) : constantCoeff (ev (n := 3) ![P, w] Y.h) = 0 :=
  const_ev (constant_zero_two_points P hP hw) (h_const Y)

theorem QQ_eq (Y : FBChart C V O dd) : QQ Y = ex (ev (n := 3) ![m3 Y.B.G V.l, p3 1] Y.h +
    ev (n := 3) ![m3 Y.B.G V.l, p3 2] Y.h - ev (n := 3) ![m3 Y.B.G V.l, SS Y.B.G] Y.h) := by
  have ha : Z0 (![m3 Y.B.G V.l, p3 1, p3 2] : Fin 3 → Pt C 3 dd) := fun k j => by
    fin_cases k
    · exact triple_multiplication_constantCoeff _ _ j
    · exact z0p3 1 j
    · exact z0p3 2 j
  have hE0 : constantCoeff (ev (n := 3) ![p3 0, p3 1] Y.h + ev (n := 3) ![p3 0, p3 2] Y.h -
      ev (n := 3) ![p3 0, SS Y.B.G] Y.h) = 0 := by
    rw [map_sub, map_add, eval_height_constantCoeff Y (z0p3 0) (z0p3 1), eval_height_constantCoeff Y (z0p3 0) (z0p3 2), eval_height_constantCoeff Y (z0p3 0) (triple_sum_constantCoeff _)]
    simp
  unfold QQ
  rw [hph2, ev_ex ha _ hE0, ev_sub ha, ev_add ha, ev_ev (constant_zero_two_points _ (z0p3 0) (z0p3 1)) ha,
    ev_ev (constant_zero_two_points _ (z0p3 0) (z0p3 2)) ha, ev_ev (constant_zero_two_points _ (z0p3 0) (triple_sum_constantCoeff _)) ha]
  have e1 : (fun k j => ev ![m3 Y.B.G V.l, p3 1, p3 2] ((![p3 0, p3 1] : Fin 2 → Pt C 3 dd) k j)) =
      ![m3 Y.B.G V.l, p3 1] := by
    funext k j; fin_cases k
    · exact ev_X ha 0 j
    · exact ev_X ha 1 j
  have e2 : (fun k j => ev ![m3 Y.B.G V.l, p3 1, p3 2] ((![p3 0, p3 2] : Fin 2 → Pt C 3 dd) k j)) =
      ![m3 Y.B.G V.l, p3 2] := by
    funext k j; fin_cases k
    · exact ev_X ha 0 j
    · exact ev_X ha 2 j
  have e3 : (fun k j => ev ![m3 Y.B.G V.l, p3 1, p3 2] ((![p3 0, SS Y.B.G] : Fin 2 → Pt C 3 dd) k j)) =
      ![m3 Y.B.G V.l, SS Y.B.G] := by
    funext k j; fin_cases k
    · exact ev_X ha 0 j
    · show ev ![m3 Y.B.G V.l, p3 1, p3 2] (ev (n := 3) ![p3 1, p3 2] (Y.B.G.F j)) = SS Y.B.G j
      rw [ev_ev (z0_pp 1 2) ha]
      congr 1
      funext k' m; fin_cases k'
      · exact ev_X ha 1 m
      · exact ev_X ha 2 m
  rw [e1, e2, e3]

theorem ident (Y : FBChart C V O dd) :
    UU Y (SS Y.B.G) * QQ Y = UU Y (p3 1) * UU Y (p3 2) * Y.B.ph2 ^ V.l := by
  have hm := triple_multiplication_constantCoeff Y.B.G V.l
  set a := ev (n := 3) ![m3 Y.B.G V.l, SS Y.B.G] Y.h with ha
  set b1 := ev (n := 3) ![m3 Y.B.G V.l, p3 1] Y.h with hb1
  set b2 := ev (n := 3) ![m3 Y.B.G V.l, p3 2] Y.h with hb2
  set c0 := ev (n := 3) ![p3 0, SS Y.B.G] Y.h with hc0
  set c1 := ev (n := 3) ![p3 0, p3 1] Y.h with hc1
  set c2 := ev (n := 3) ![p3 0, p3 2] Y.h with hc2
  have za : constantCoeff a = 0 := eval_height_constantCoeff Y hm (triple_sum_constantCoeff _)
  have zb1 : constantCoeff b1 = 0 := eval_height_constantCoeff Y hm (z0p3 1)
  have zb2 : constantCoeff b2 = 0 := eval_height_constantCoeff Y hm (z0p3 2)
  have zc0 : constantCoeff c0 = 0 := eval_height_constantCoeff Y (z0p3 0) (triple_sum_constantCoeff _)
  have zc1 : constantCoeff c1 = 0 := eval_height_constantCoeff Y (z0p3 0) (z0p3 1)
  have zc2 : constantCoeff c2 = 0 := eval_height_constantCoeff Y (z0p3 0) (z0p3 2)
  have zs : ∀ (c : C) (f : PS C 3 dd), constantCoeff f = 0 → constantCoeff (c • f) = 0 := fun c f hf => by
    rw [show c • f = MvPowerSeries.C c * f from (MvPowerSeries.smul_eq_C_mul f c), map_mul, hf, mul_zero]
  have zE : constantCoeff (c1 + c2 - c0) = 0 := by rw [map_sub, map_add, zc1, zc2, zc0]; simp
  rw [UU_eq _ _ (triple_sum_constantCoeff _), UU_eq _ _ (z0p3 1), UU_eq _ _ (z0p3 2), QQ_eq, hph2, ← hc0, ← hc1, ← hc2, ← ha,
    ← hb1, ← hb2, ← ex_nsmul _ zE V.l,
    ← ex_add _ _ (by rw [map_sub, za, zs _ _ zc0, sub_zero]) (by rw [map_sub, map_add, zb1, zb2, za]; simp),
    ← ex_add _ _ (by rw [map_sub, zb1, zs _ _ zc1, sub_zero]) (by rw [map_sub, zb2, zs _ _ zc2, sub_zero]),
    ← ex_add _ _ (by rw [map_add, map_sub, map_sub, zb1, zb2, zs _ _ zc1, zs _ _ zc2]; simp)
      (by rw [map_nsmul, zE, nsmul_zero])]
  congr 1
  rw [Nat.cast_smul_eq_nsmul C, Nat.cast_smul_eq_nsmul C, Nat.cast_smul_eq_nsmul C]
  simp only [nsmul_sub, nsmul_add]
  abel

end Formalism.L2.FormalSeriesBounds.FunEq
