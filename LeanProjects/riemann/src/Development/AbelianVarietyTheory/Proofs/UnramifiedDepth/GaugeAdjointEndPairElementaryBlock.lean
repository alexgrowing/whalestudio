import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.NondegenerateCharts
import Formalism.LocalToGlobal.CharacterGerms.RowTieSelf
import Formalism.LocalToGlobal.CharacterGerms.BlockAdmissibleChart
import Formalism.LocalToGlobal.CharacterGerms.NegMem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IntSOfMulEqOne

noncomputable section

open scoped BigOperators
open Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw GlobalTheory.RowVal ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.RowLaw.EndBlock

open MvPowerSeries

variable {C : Type} [Field C]

theorem eq_zero_of_van {τ : Type} {f : MvPowerSeries τ C} (h : Van (∅ : Set τ) f) : f = 0 := by
  ext ν
  rw [h ν (fun _ _ => Set.notMem_empty _)]
  simp

theorem subst_zero' {σ τ : Type} [Finite σ] {f : MvPowerSeries σ C} (hf : constantCoeff f = 0) :
    subst (fun _ : σ => (0 : MvPowerSeries τ C)) f = 0 :=
  eq_zero_of_van (Van.subst Set.univ (fun _ => map_zero _) (fun _ _ ν _ => by simp) (van_univ hf))

section General

variable {d : ℕ} {I : Fin 2 → Type} {κ : Type} [Fintype κ] (X : RawChart C d I κ)

theorem cc_lin (hlg : ∀ i, constantCoeff (X.lg i) = 0) (M : Matrix κ κ C) {τ : Type}
    {a : κ → MvPowerSeries τ C} (ha : ∀ i, constantCoeff (a i) = 0) (x : κ) :
    constantCoeff (∑ y, M x y • subst a (X.lg y)) = 0 := by
  rw [map_sum]
  refine Finset.sum_eq_zero fun y _ => ?_
  rw [constantCoeff_smul, cc_subst ha, hlg, smul_zero]

theorem cc_endP (hlg : ∀ i, constantCoeff (X.lg i) = 0) (hex : ∀ i, constantCoeff (X.ex i) = 0)
    (M : Matrix κ κ C) {τ : Type} {a : κ → MvPowerSeries τ C} (ha : ∀ i, constantCoeff (a i) = 0) (i : κ) :
    constantCoeff (endP X M a i) = 0 := by
  unfold endP
  rw [cc_subst (cc_lin X hlg M ha), hex]

theorem subst_endP (hlg : ∀ i, constantCoeff (X.lg i) = 0) (M : Matrix κ κ C) {τ υ : Type} [Finite τ]
    {a : κ → MvPowerSeries τ C} (ha : ∀ i, constantCoeff (a i) = 0)
    {b : τ → MvPowerSeries υ C} (hb : ∀ i, constantCoeff (b i) = 0) (i : κ) :
    subst b (endP X M a i) = endP X M (fun k => subst b (a k)) i := by
  have hA := hasSubst_of_constantCoeff_zero ha
  have hB := hasSubst_of_constantCoeff_zero hb
  unfold endP
  rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero (cc_lin X hlg M ha)) hB]
  congr 1
  funext x
  rw [← coe_substAlgHom hB, map_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [map_smul, coe_substAlgHom hB, subst_comp_subst_apply hA hB]

theorem cc_pair {τ : Type} {a b : κ → MvPowerSeries τ C} (ha : ∀ i, constantCoeff (a i) = 0)
    (hb : ∀ i, constantCoeff (b i) = 0) (p : Fin 2 × κ) :
    constantCoeff (if p.1 = 0 then a p.2 else b p.2) = 0 := by
  split_ifs
  exacts [ha _, hb _]

theorem subst_hAt {τ υ : Type} [Finite τ] {a a' : κ → MvPowerSeries τ C} (ha : ∀ i, constantCoeff (a i) = 0)
    (ha' : ∀ i, constantCoeff (a' i) = 0)
    {b : τ → MvPowerSeries υ C} (hb : ∀ i, constantCoeff (b i) = 0) :
    subst b (hAt X a a') = hAt X (fun k => subst b (a k)) (fun k => subst b (a' k)) := by
  unfold hAt
  rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero (cc_pair ha ha'))
    (hasSubst_of_constantCoeff_zero hb)]
  congr 1
  funext p
  split_ifs <;> rfl

theorem hAt_zero_left (hh : ∀ e : Fin 2 × κ →₀ ℕ, (∀ s ∈ e.support, s.1 ≠ 0) → coeff e X.h = 0) {τ : Type}
    {b : κ → MvPowerSeries τ C} (hb : ∀ i, constantCoeff (b i) = 0) : hAt X (fun _ => 0) b = 0 := by
  refine eq_zero_of_van (Van.subst {s : Fin 2 × κ | s.1 = 0} (cc_pair (fun _ => map_zero _) hb) ?_ hh)
  intro s hs ν _
  have h0 : s.1 = 0 := hs
  rw [if_pos h0, map_zero]

theorem hAt_zero_right (hh : ∀ e : Fin 2 × κ →₀ ℕ, (∀ s ∈ e.support, s.1 ≠ 1) → coeff e X.h = 0) {τ : Type}
    {a : κ → MvPowerSeries τ C} (ha : ∀ i, constantCoeff (a i) = 0) : hAt X a (fun _ => 0) = 0 := by
  refine eq_zero_of_van (Van.subst {s : Fin 2 × κ | s.1 = 1} (cc_pair ha (fun _ => map_zero _)) ?_ hh)
  intro s hs ν _
  have h1 : s.1 = 1 := hs
  rw [if_neg (by rw [h1]; decide), map_zero]

theorem cc_hAt (hh : ∀ e : Fin 2 × κ →₀ ℕ, (∀ s ∈ e.support, s.1 ≠ 0) → coeff e X.h = 0) {τ : Type}
    {a b : κ → MvPowerSeries τ C} (ha : ∀ i, constantCoeff (a i) = 0) (hb : ∀ i, constantCoeff (b i) = 0) :
    constantCoeff (hAt X a b) = 0 := by
  unfold hAt
  rw [cc_subst (cc_pair ha hb), ← coeff_zero_eq_constantCoeff_apply]
  exact hh 0 (by simp)

end General

section Square

variable {dd : ℕ}

theorem subst_inCol {τ : Type} {a : Fin 2 × Fin dd → MvPowerSeries τ C} (ha : ∀ i, constantCoeff (a i) = 0)
    (col : Fin 2) (f : MvPowerSeries (Fin dd) C) :
    subst a (inCol col f) = subst (fun k => a (col, k)) f := by
  have hA := hasSubst_of_constantCoeff_zero ha
  unfold inCol
  rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _) hA]
  congr 1
  funext k
  rw [subst_X hA]

variable {d d' : ℕ} {I I' : Fin 2 → Type} (X : RawChart C d I (Fin dd)) (Z : RawChart C d' I' (Fin 2 × Fin dd))

theorem matrixEnd_block (hlg : ∀ x, Z.lg x = inCol x.1 (X.lg x.2)) (hex : ∀ x, Z.ex x = inCol x.1 (X.ex x.2))
    (hlg0 : ∀ i, constantCoeff (X.lg i) = 0) (hex0 : ∀ i, constantCoeff (X.ex i) = 0) (r s : Fin 2)
    (M : Matrix (Fin dd) (Fin dd) C) {τ : Type} {a : Fin 2 × Fin dd → MvPowerSeries τ C}
    (ha : ∀ i, constantCoeff (a i) = 0) (col : Fin 2) (i : Fin dd) :
    endP Z (Matrix.of fun x y : Fin 2 × Fin dd => if x.1 = r ∧ y.1 = s then M x.2 y.2 else 0) a (col, i) =
      if col = r then endP X M (fun k => a (s, k)) i else 0 := by
  have hZ : ∀ x, constantCoeff (Z.lg x) = 0 := fun x => by
    rw [hlg, inCol, cc_subst (fun _ => constantCoeff_X _), hlg0]
  unfold endP
  rw [hex, subst_inCol (cc_lin Z hZ _ ha)]
  split_ifs with hc
  · congr 1
    funext k
    rw [Fintype.sum_prod_type, Finset.sum_eq_single s]
    · refine Finset.sum_congr rfl fun y _ => ?_
      rw [hlg, subst_inCol ha]
      simp [hc]
    · intro t _ ht
      simp [ht]
    · simp
  · simp only [Matrix.of_apply, hc, false_and, if_false, zero_smul, Finset.sum_const_zero]
    exact subst_zero' (hex0 i)

theorem hAt_square (hh : Z.h = ∑ col, hCol col X.h) {τ : Type} {a b : Fin 2 × Fin dd → MvPowerSeries τ C}
    (ha : ∀ i, constantCoeff (a i) = 0) (hb : ∀ i, constantCoeff (b i) = 0) :
    hAt Z a b = ∑ col, hAt X (fun k => a (col, k)) (fun k => b (col, k)) := by
  have hA := hasSubst_of_constantCoeff_zero (cc_pair ha hb)
  unfold hAt
  rw [hh, ← coe_substAlgHom hA, map_sum]
  refine Finset.sum_congr rfl fun col _ => ?_
  rw [coe_substAlgHom hA, hCol,
    subst_comp_subst_apply (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _) hA]
  congr 1
  funext q
  rw [subst_X hA]

theorem isEnd_block_raw [CharZero C] (V : VF C) (hlg : ∀ x, Z.lg x = inCol x.1 (X.lg x.2))
    (hex : ∀ x, Z.ex x = inCol x.1 (X.ex x.2)) (hh : Z.h = ∑ col, hCol col X.h)
    (hlg0 : ∀ i, constantCoeff (X.lg i) = 0) (hex0 : ∀ i, constantCoeff (X.ex i) = 0)
    (hax : ∀ (g : Fin 2) (e : Fin 2 × Fin dd →₀ ℕ), (∀ s ∈ e.support, s.1 ≠ g) → coeff e X.h = 0)
    (r s : Fin 2) (M M' : Matrix (Fin dd) (Fin dd) C) (H : IsEnd X V M M') :
    IsEnd Z V (Matrix.of fun x y : Fin 2 × Fin dd => if x.1 = r ∧ y.1 = s then M x.2 y.2 else 0)
      (Matrix.of fun x y : Fin 2 × Fin dd => if x.1 = s ∧ y.1 = r then M' x.2 y.2 else 0) := by
  have hint : ∀ (r s : Fin 2) (M : Matrix (Fin dd) (Fin dd) C),
      (∀ i, IntS V (endP X M (MvPowerSeries.X : Fin dd → MvPowerSeries (Fin dd) C) i)) →
      ∀ x, IntS V (endP Z (Matrix.of fun x y : Fin 2 × Fin dd => if x.1 = r ∧ y.1 = s then M x.2 y.2 else 0)
        (MvPowerSeries.X : Fin 2 × Fin dd → MvPowerSeries (Fin 2 × Fin dd) C) x) := by
    rintro r s M hM ⟨col, i⟩
    rw [matrixEnd_block X Z hlg hex hlg0 hex0 r s M (fun _ => constantCoeff_X _)]
    split_ifs
    · have hb : ∀ k : Fin dd, constantCoeff (MvPowerSeries.X (s, k) : MvPowerSeries (Fin 2 × Fin dd) C) = 0 :=
        fun _ => constantCoeff_X _
      have h1 := intS_subst hb (fun _ => intS_X _) (hM i)
      rw [subst_endP X hlg0 M (fun _ => constantCoeff_X _) hb] at h1
      simpa only [subst_X (hasSubst_of_constantCoeff_zero hb)] using h1
    · exact intS_zero
  refine ⟨hint r s M H.1, hint s r M' H.2.1, ?_⟩
  have hZ : ∀ x, constantCoeff (Z.lg x) = 0 := fun x => by
    rw [hlg, inCol, cc_subst (fun _ => constantCoeff_X _), hlg0]
  have hZ' : ∀ x, constantCoeff (Z.ex x) = 0 := fun x => by
    rw [hex, inCol, cc_subst (fun _ => constantCoeff_X _), hex0]
  have hg : ∀ (κ : Type) (j : Fin 2) (x : κ), constantCoeff (gp C κ j x) = 0 := fun _ _ _ => constantCoeff_X _
  have hb : ∀ q : Fin 2 × Fin dd, constantCoeff (MvPowerSeries.X (q.1, (if q.1 = 0 then s else r, q.2)) :
      MvPowerSeries (Fin 2 × (Fin 2 × Fin dd)) C) = 0 := fun _ => constantCoeff_X _
  have hB := hasSubst_of_constantCoeff_zero hb
  have h1 := intS_subst hb (fun _ => intS_X _) H.2.2
  rw [subst_mvExp hb (by
      rw [map_sub, cc_hAt X (hax 0) (cc_endP X hlg0 hex0 M (hg _ 0)) (hg _ 1),
        cc_hAt X (hax 0) (hg _ 0) (cc_endP X hlg0 hex0 M' (hg _ 1)), sub_zero]),
    subst_sub hB, subst_hAt X (cc_endP X hlg0 hex0 M (hg _ 0)) (hg _ 1) hb,
    subst_hAt X (hg _ 0) (cc_endP X hlg0 hex0 M' (hg _ 1)) hb] at h1
  simp only [subst_endP X hlg0 _ (hg _ _) hb] at h1
  simp only [gp, subst_X hB, if_true, one_ne_zero, if_false] at h1
  rw [hAt_square X Z hh (cc_endP Z hZ hZ' _ (hg _ 0)) (hg _ 1),
    hAt_square X Z hh (hg _ 0) (cc_endP Z hZ hZ' _ (hg _ 1)),
    Finset.sum_eq_single r, Finset.sum_eq_single s]
  · simp only [matrixEnd_block X Z hlg hex hlg0 hex0 _ _ _ (hg _ _), if_true]
    exact h1
  · intro t _ ht
    simp only [matrixEnd_block X Z hlg hex hlg0 hex0 _ _ _ (hg _ _), if_neg ht]
    exact hAt_zero_right X (hax 1) (fun _ => hg _ _ _)
  · simp
  · intro t _ ht
    simp only [matrixEnd_block X Z hlg hex hlg0 hex0 _ _ _ (hg _ _), if_neg ht]
    exact hAt_zero_left X (hax 0) (fun _ => hg _ _ _)
  · simp

end Square

theorem isEnd_block : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ)
    (Y : FBChart C V O dd) (d : ℕ) (I0 : Type) [Fintype I0] (p : SelfData Y d I0) (d' : ℕ) (I : Fin 2 → Type)
    (X : RawChart C d' I (Fin dd)), (X.lg = fun i => un1 (Y.lg i)) → (X.ex = fun i => un1 (Y.ex i)) → X.h = Y.h →
    ∀ (r s : Fin 2) (M M' : Matrix (Fin dd) (Fin dd) C), IsEnd X V M M' →
    IsEnd (Y.rawSelf p) V
      (Matrix.of fun x y : Fin 2 × Fin dd => if x.1 = r ∧ y.1 = s then M x.2 y.2 else 0)
      (Matrix.of fun x y : Fin 2 × Fin dd => if x.1 = s ∧ y.1 = r then M' x.2 y.2 else 0) := by
  intro C _ _ V O _ _ dd Y d I0 _ p d' I X hlg hex hh r s M M' H
  refine isEnd_block_raw X (Y.rawSelf p) V (fun x => by rw [hlg]; rfl) (fun x => by rw [hex]; rfl)
    (by rw [hh]; rfl) (fun i => ?_) (fun i => ?_) (fun g => ?_) r s M M' H
  · rw [hlg]
    show constantCoeff (un1 (Y.lg i)) = 0
    rw [constantCoeff_uncurry, ← coeff_zero_eq_constantCoeff_apply, Y.lg_lin i 0 (by simp),
      coeff_zero_eq_constantCoeff_apply, constantCoeff_X]
  · rw [hex]
    show constantCoeff (un1 (Y.ex i)) = 0
    rw [constantCoeff_uncurry]
    exact Y.ex_const i
  · rw [hh]
    fin_cases g
    · refine coeff_of_ev_zero Y.h 0 ![0, pt C dd 0] rfl ?_ Y.gauge.ax0
      intro g' hg'
      rw [fin_two_eq_one_sub_of_ne' 0 g' hg']
      rfl
    · refine coeff_of_ev_zero Y.h 1 ![pt C dd 0, 0] rfl ?_ Y.gauge.ax1
      intro g' hg'
      rw [fin_two_eq_one_sub_of_ne' 1 g' hg']
      rfl

end GlobalTheory.RowLaw.EndBlock
