import Formalism.LocalToGlobal.CharacterGerms.FirstVanishingAt
import Formalism.LocalToGlobal.CharacterGerms.PderivDoubleMultiplicationJacobian
import Formalism.LocalToGlobal.CharacterGerms.RowTieCartAdd

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

def zl {C : Type} [Field C] {dd : ℕ} (v : Fin dd → C) (F : PS C 2 dd) : PS C 1 dd :=
  ∑ j, MvPowerSeries.C (v j) * ev (n := 1) ![pt C dd 0, 0] (MvPowerSeries.pderiv C ((1 : Fin 2), j) F)

namespace SelfAdjointLinearTerm

open PartialDerivEval FirstUnitSeriesIntegrality MulLFrob LiftedCoordinateEvaluation MvPowerSeries

variable {C : Type} [Field C] {dd : ℕ}

theorem snd_map (ν : Fin 1 × Fin dd →₀ ℕ) :
    (ν.mapDomain Prod.snd).mapDomain (fun x : Fin dd => ((0 : Fin 1), x)) = ν := by
  rw [← Finsupp.mapDomain_comp]
  have e : ((fun x : Fin dd => ((0 : Fin 1), x)) ∘ Prod.snd) = id := by
    funext p
    exact Prod.ext (Subsingleton.elim _ _) rfl
  rw [e, Finsupp.mapDomain_id]

theorem snd_mapDomain_mapDomain (ν : Fin 1 × Fin dd →₀ ℕ) :
    (ν.mapDomain Prod.snd).mapDomain (fun x : Fin dd => ((0 : Fin 2), x)) =
      ν.mapDomain (fun q : Fin 1 × Fin dd => ((0 : Fin 2), q.2)) := by
  rw [← Finsupp.mapDomain_comp]
  rfl

end SelfAdjointLinearTerm

open SelfAdjointLinearTerm in
theorem coeff_zl {C : Type} [Field C] {dd : ℕ} (v : Fin dd → C) (F : PS C 2 dd) (ν : Fin 1 × Fin dd →₀ ℕ) :
    MvPowerSeries.coeff ν (zl v F) = ∑ j, v j * MvPowerSeries.coeff
      (ν.mapDomain (fun q : Fin 1 × Fin dd => ((0 : Fin 2), q.2)) + Finsupp.single ((1 : Fin 2), j) 1) F := by
  unfold zl
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [MvPowerSeries.coeff_C_mul]
  conv_lhs => rw [← snd_map ν]
  rw [coeff_eval_second_zero, MvPowerSeries.coeff_pderiv, snd_mapDomain_mapDomain]
  have h0 : (ν.mapDomain fun q : Fin 1 × Fin dd => ((0 : Fin 2), q.2)) ((1 : Fin 2), j) = 0 := by
    apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨x, hx⟩
    have h01 : (0 : Fin 2) = 1 := congrArg Prod.fst hx
    exact absurd h01 (by decide)
  rw [h0]
  simp

namespace SelfAdjointLinearTerm

open PartialDerivEval FirstUnitSeriesIntegrality MulLFrob LiftedCoordinateEvaluation MvPowerSeries

variable {C : Type} [Field C] [CharZero C] {dd : ℕ}

theorem aux_statement_9 : Z0 (![pt C dd 0, 0] : Fin 2 → Pt C 1 dd) := by
  intro k i
  fin_cases k
  · simp [pt]
  · simp

theorem zl_sub (v : Fin dd → C) (F G : PS C 2 dd) : zl v (F - G) = zl v F - zl v G := by
  have hS : MvPowerSeries.HasSubst (fun p : Fin 2 × Fin dd => (![pt C dd 0, 0] : Fin 2 → Pt C 1 dd) p.1 p.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun p => aux_statement_9 p.1 p.2)
  simp only [zl, ev, map_sub, MvPowerSeries.subst_sub hS, mul_sub, Finset.sum_sub_distrib]

theorem zl_smul (v : Fin dd → C) (c : C) (F : PS C 2 dd) : zl v (c • F) = c • zl v F := by
  have hS : MvPowerSeries.HasSubst (fun p : Fin 2 × Fin dd => (![pt C dd 0, 0] : Fin 2 → Pt C 1 dd) p.1 p.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun p => aux_statement_9 p.1 p.2)
  simp only [zl, ev, Derivation.map_smul, LinearMap.map_smul, MvPowerSeries.subst_smul hS, Finset.smul_sum,
    mul_smul_comm]

theorem zl_expS (v : Fin dd → C) {f : PS C 2 dd} (hf : constantCoeff f = 0)
    (hf0 : ev (n := 1) ![pt C dd 0, 0] f = 0) : zl v (FB.expS C f) = zl v f := by
  unfold zl
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pderiv_expS hf, ev_mul aux_statement_9, expS_eq, ev_ex aux_statement_9 f hf, hf0, ex_zero, one_mul]

def PAB (A B : Pt C 1 dd) : Fin 2 → Pt C 2 dd := ![comp1 A (pt C (n := 2) dd 0), comp1 B (pt C (n := 2) dd 1)]

theorem constant_zero_comp_coordinate {n : ℕ} {A : Pt C 1 dd} (hA : ∀ i, constantCoeff (A i) = 0) (k : Fin n) (i : Fin dd) :
    constantCoeff (comp1 A (pt C (n := n) dd k) i) = 0 := by
  simp only [comp1, ev]
  have hc : ∀ p : Fin 1 × Fin dd, constantCoeff ((![pt C dd k] : Fin 1 → Pt C n dd) p.1 p.2) = 0 := by
    intro p
    simp only [Matrix.cons_val_fin_one, pt, MvPowerSeries.constantCoeff_X]
  apply MvPowerSeries.constantCoeff_subst_eq_zero
  · exact MvPowerSeries.hasSubst_of_constantCoeff_zero hc
  · exact hc
  · exact hA i

theorem zPAB {A B : Pt C 1 dd} (hA : ∀ i, constantCoeff (A i) = 0) (hB : ∀ i, constantCoeff (B i) = 0) :
    Z0 (PAB A B) := by
  intro k i
  fin_cases k
  · simpa [PAB] using constant_zero_comp_coordinate hA 0 i
  · simpa [PAB] using constant_zero_comp_coordinate hB 1 i

theorem product_points_at_zero {A B : Pt C 1 dd} (hB : ∀ i, constantCoeff (B i) = 0) :
    (fun k i => ev (n := 1) ![pt C dd 0, 0] (PAB A B k i)) = (![A, 0] : Fin 2 → Pt C 1 dd) := by
  funext k i
  fin_cases k
  · show ev (n := 1) ![pt C dd 0, 0] (ev ![pt C (n := 2) dd 0] (A i)) = A i
    rw [ev_ev (z0_1 _ fun j => z0_pt 0 j) aux_statement_9]
    have : (fun (k : Fin 1) (i : Fin dd) => ev (n := 1) ![pt C dd 0, 0] ((![pt C (n := 2) dd 0] : Fin 1 → Pt C 2 dd) k i)) =
        ![pt C (n := 1) dd 0] := by
      funext k i
      fin_cases k
      exact ev_X aux_statement_9 0 i
    rw [this, germEval_oneStandardPoint_self]
  · show ev (n := 1) ![pt C dd 0, 0] (ev ![pt C (n := 2) dd 1] (B i)) = 0
    rw [ev_ev (z0_1 _ fun j => z0_pt 1 j) aux_statement_9]
    have : (fun (k : Fin 1) (i : Fin dd) => ev (n := 1) ![pt C dd 0, 0] ((![pt C (n := 2) dd 1] : Fin 1 → Pt C 2 dd) k i)) =
        ![(0 : Pt C 1 dd)] := by
      funext k i
      fin_cases k
      exact ev_X aux_statement_9 1 i
    rw [this, ev_zero_pt, hB i, map_zero]

theorem d_A (A : Pt C 1 dd) (j k : Fin dd) :
    pderiv C ((1 : Fin 2), j) (comp1 A (pt C (n := 2) dd 0) k) = 0 := by
  show pderiv C ((1 : Fin 2), j) (ev ![pt C (n := 2) dd 0] (A k)) = 0
  rw [pderiv_eval_single (fun j => z0_pt 0 j)]
  refine Finset.sum_eq_zero fun m _ => ?_
  rw [pderiv_pt_ne _ _ _ (show (0 : Fin 2) ≠ 1 by decide), mul_zero]

theorem d_B (B : Pt C 1 dd) (j k : Fin dd) :
    pderiv C ((1 : Fin 2), j) (comp1 B (pt C (n := 2) dd 1) k) =
      ev ![pt C (n := 2) dd 1] (pderiv C ((0 : Fin 1), j) (B k)) := by
  show pderiv C ((1 : Fin 2), j) (ev ![pt C (n := 2) dd 1] (B k)) = _
  rw [pderiv_eval_single (fun j => z0_pt 1 j), Finset.sum_eq_single j]
  · rw [pderiv_pt_same, if_pos rfl, mul_one]
  · intro m _ hm
    rw [pderiv_pt_same, if_neg hm, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem eval_pderiv_constant_linear (B : Pt C 1 dd) (j k : Fin dd) :
    ev (n := 1) ![pt C dd 0, 0] (ev ![pt C (n := 2) dd 1] (pderiv C ((0 : Fin 1), j) (B k))) =
      MvPowerSeries.C (coeff (Finsupp.single ((0 : Fin 1), j) 1) (B k)) := by
  rw [ev_ev (z0_1 _ fun j => z0_pt 1 j) aux_statement_9]
  have : (fun (k : Fin 1) (i : Fin dd) => ev (n := 1) ![pt C dd 0, 0] ((![pt C (n := 2) dd 1] : Fin 1 → Pt C 2 dd) k i)) =
      ![(0 : Pt C 1 dd)] := by
    funext k i
    fin_cases k
    exact ev_X aux_statement_9 1 i
  rw [this, ev_zero_pt, ← coeff_zero_eq_constantCoeff_apply, coeff_pderiv]
  simp

variable {V : VF C} {O : Type} [CommRing O] [StarRing O]

theorem zl_hAB (Y : FBChart C V O dd) {A B : Pt C 1 dd} (hA : ∀ i, constantCoeff (A i) = 0)
    (hB : ∀ i, constantCoeff (B i) = 0) (v : Fin dd → C) :
    zl v (ev (PAB A B) Y.h) = -ev (n := 1) ![A] (Y.sgP (linAct B v)) := by
  rw [ev_sgP Y _ A hA, neg_neg]
  unfold zl
  have h1 : ∀ j, ev (n := 1) ![pt C dd 0, 0] (pderiv C ((1 : Fin 2), j) (ev (PAB A B) Y.h)) =
      ∑ k, ev (n := 1) ![A, 0] (pderiv C ((1 : Fin 2), k) Y.h) *
        MvPowerSeries.C (coeff (Finsupp.single ((0 : Fin 1), j) 1) (B k)) := by
    intro j
    rw [pderiv_eval_pair (zPAB hA hB)]
    have e0 : ∑ k, ev (PAB A B) (pderiv C ((0 : Fin 2), k) Y.h) * pderiv C ((1 : Fin 2), j) (PAB A B 0 k) = 0 :=
      Finset.sum_eq_zero fun k _ => by
        rw [show PAB A B 0 k = comp1 A (pt C (n := 2) dd 0) k from rfl, d_A, mul_zero]
    rw [e0, zero_add, ev_sum aux_statement_9]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show PAB A B 1 k = comp1 B (pt C (n := 2) dd 1) k from rfl, d_B, ev_mul aux_statement_9, eval_pderiv_constant_linear,
      ev_ev (zPAB hA hB) aux_statement_9, product_points_at_zero hB]
  simp only [h1, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold linAct
  rw [map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul]
  ring

theorem height_at_zero_product (Y : FBChart C V O dd) {A B : Pt C 1 dd} (hA : ∀ i, constantCoeff (A i) = 0)
    (hB : ∀ i, constantCoeff (B i) = 0) : ev (n := 1) ![pt C dd 0, 0] (ev (PAB A B) Y.h) = 0 := by
  rw [ev_ev (zPAB hA hB) aux_statement_9, product_points_at_zero hB]
  have h := congrArg (ev (n := 1) ![A]) Y.gauge.ax1
  rw [ev_ev aux_statement_9 (z0_1 A hA), ev_zero (z0_1 A hA)] at h
  have : (fun (k : Fin 2) (i : Fin dd) => ev (n := 1) ![A] ((![pt C dd 0, 0] : Fin 2 → Pt C 1 dd) k i)) =
      (![A, 0] : Fin 2 → Pt C 1 dd) := by
    funext k i
    fin_cases k
    · exact ev_X (z0_1 A hA) 0 i
    · exact ev_zero (z0_1 A hA)
  rw [this] at h
  exact h

theorem const_hAB (Y : FBChart C V O dd) {A B : Pt C 1 dd} (hA : ∀ i, constantCoeff (A i) = 0)
    (hB : ∀ i, constantCoeff (B i) = 0) : constantCoeff (ev (PAB A B) Y.h) = 0 :=
  const_ev (zPAB hA hB) (h_const Y)

theorem comp1_identity_left {n : ℕ} (k : Fin n) : comp1 (pt C (n := 1) dd 0) (pt C (n := n) dd k) = pt C dd k := by
  funext i
  simp only [comp1, ev, pt]
  rw [MvPowerSeries.subst_X (MvPowerSeries.hasSubst_of_constantCoeff_zero (fun p => by
    simp only [Matrix.cons_val_fin_one, pt, MvPowerSeries.constantCoeff_X]))]
  rfl

theorem linAct_id (v : Fin dd → C) : linAct (pt C (n := 1) dd 0) v = v := by
  funext i
  unfold linAct
  rw [Finset.sum_eq_single i]
  · show coeff (Finsupp.single ((0 : Fin 1), i) 1) (X ((0 : Fin 1), i) : PS C 1 dd) * v i = v i
    rw [coeff_X, if_pos rfl, one_mul]
  · intro j _ hj
    show coeff (Finsupp.single ((0 : Fin 1), j) 1) (X ((0 : Fin 1), i) : PS C 1 dd) * v j = 0
    rw [coeff_X, if_neg, zero_mul]
    intro h
    apply hj
    have := (Finsupp.single_left_inj (one_ne_zero)).1 h
    exact (Prod.mk.inj this).2
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem zId : ∀ i, constantCoeff (pt C (n := 1) dd 0 i) = 0 := fun i => by simp [pt]

end SelfAdjointLinearTerm

open SelfAdjointLinearTerm PartialDerivEval FirstUnitSeriesIntegrality MulLFrob in

theorem linear_part_first_unit {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
    (Y : FBChart C V O dd) (v : Fin dd → C) :
    zl v Y.u1 = (V.l : C) • Y.sgP v - ev (n := 1) ![mulL Y.B.G.F V.l] (Y.sgP v) := by
  have hM : ∀ i, MvPowerSeries.constantCoeff (mulL Y.B.G.F V.l i) = 0 := multiplication_constantCoeff_zero Y.B.G V.l
  have e1 : (![comp1 (mulL Y.B.G.F V.l) (pt C (n := 2) dd 0), pt C dd 1] : Fin 2 → Pt C 2 dd) =
      PAB (mulL Y.B.G.F V.l) (pt C (n := 1) dd 0) := by
    unfold PAB
    rw [comp1_identity_left]
  have e2 : ev (PAB (pt C (n := 1) dd 0) (pt C (n := 1) dd 0)) Y.h = Y.h := by
    unfold PAB
    rw [comp1_identity_left, comp1_identity_left, PartialDerivEval.eval_points_two]
  have e3 : ev (n := 2) ![comp1 (mulL Y.B.G.F V.l) (pt C (n := 2) dd 0), pt C dd 1] Y.h - (V.l : C) • Y.h =
      ev (PAB (mulL Y.B.G.F V.l) (pt C (n := 1) dd 0)) Y.h -
        (V.l : C) • ev (PAB (pt C (n := 1) dd 0) (pt C (n := 1) dd 0)) Y.h := by
    rw [e1, e2]
  unfold FBChart.u1
  rw [e3, zl_expS v
      (by rw [map_sub, const_hAB Y hM zId, MvPowerSeries.smul_eq_C_mul, map_mul, const_hAB Y zId zId, mul_zero,
        sub_zero])
      (by rw [ev_sub aux_statement_9, height_at_zero_product Y hM zId, MvPowerSeries.smul_eq_C_mul, ev_mul aux_statement_9, height_at_zero_product Y zId zId, mul_zero,
        sub_zero]),
    zl_sub, zl_smul, zl_hAB Y hM zId, zl_hAB Y zId zId, linAct_id, germEval_oneStandardPoint_self, smul_neg]
  ring

open SelfAdjointLinearTerm PartialDerivEval FirstUnitSeriesIntegrality MulLFrob in

theorem constant_zero_first_zero_self {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
    (Y : FBChart C V O dd) (e eb : Pt C 1 dd) (he0 : ∀ i, MvPowerSeries.constantCoeff (e i) = 0)
    (heb0 : ∀ i, MvPowerSeries.constantCoeff (eb i) = 0) (v : Fin dd → C) :
    zl v (FB.expS C (ev (n := 2) ![comp1 e (pt C dd 0), pt C dd 1] Y.h -
      ev (n := 2) ![pt C dd 0, comp1 eb (pt C dd 1)] Y.h)) =
      Y.sgP (linAct eb v) - ev (n := 1) ![e] (Y.sgP v) := by
  have e1 : (![comp1 e (pt C (n := 2) dd 0), pt C dd 1] : Fin 2 → Pt C 2 dd) = PAB e (pt C (n := 1) dd 0) := by
    unfold PAB
    rw [comp1_identity_left]
  have e2 : (![pt C (n := 2) dd 0, comp1 eb (pt C dd 1)] : Fin 2 → Pt C 2 dd) = PAB (pt C (n := 1) dd 0) eb := by
    unfold PAB
    rw [comp1_identity_left]
  rw [e1, e2, zl_expS v
      (by rw [map_sub, const_hAB Y he0 zId, const_hAB Y zId heb0, sub_zero])
      (by rw [ev_sub aux_statement_9, height_at_zero_product Y he0 zId, height_at_zero_product Y zId heb0, sub_zero]),
    zl_sub, zl_hAB Y he0 zId, zl_hAB Y zId heb0, linAct_id, germEval_oneStandardPoint_self]
  ring

end Formalism.L2.FormalSeriesBounds
