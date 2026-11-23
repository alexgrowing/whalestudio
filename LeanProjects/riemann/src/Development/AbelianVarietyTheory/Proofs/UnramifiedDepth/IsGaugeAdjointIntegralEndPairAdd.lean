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
open Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds GlobalTheory.RowLaw GlobalTheory.RowVal MvPowerSeries

namespace GlobalTheory.RowLaw.EndSum

variable {C : Type} [Field C] {d : ℕ} {I : Fin 2 → Type} {κ : Type} [Fintype κ]
  {X : RawChart C d I κ} {V : VF C}

theorem pair_cc {τ : Type} {a b : κ → MvPowerSeries τ C} (ha : ∀ s, constantCoeff (a s) = 0)
    (hb : ∀ s, constantCoeff (b s) = 0) (p : Fin 2 × κ) :
    constantCoeff (if p.1 = 0 then a p.2 else b p.2) = 0 := by
  split_ifs
  · exact ha _
  · exact hb _

theorem gp_cc {n : ℕ} (j : Fin n) (x : κ) : constantCoeff (gp C κ j x) = 0 := constantCoeff_X _

theorem lg_cc (h : RLaw X V) (i : κ) : constantCoeff (X.lg i) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, h.lin i 0 (by simp), coeff_zero_eq_constantCoeff_apply,
    constantCoeff_X]

theorem h_cc (h : RLaw X V) : constantCoeff X.h = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply]
  exact h.axes 0 0 (by simp)

theorem sum_cc (h : RLaw X V) {τ : Type} {a b : κ → MvPowerSeries τ C}
    (ha : ∀ s, constantCoeff (a s) = 0) (hb : ∀ s, constantCoeff (b s) = 0) (x : κ) :
    constantCoeff (subst a (X.lg x) + subst b (X.lg x)) = 0 := by
  rw [map_add, cc_subst ha, cc_subst hb, lg_cc h, add_zero]

theorem lin_cc (h : RLaw X V) (M : Matrix κ κ C) {τ : Type} {a : κ → MvPowerSeries τ C}
    (ha : ∀ s, constantCoeff (a s) = 0) (x : κ) :
    constantCoeff (∑ y, M x y • subst a (X.lg y)) = 0 := by
  rw [map_sum]
  refine Finset.sum_eq_zero fun y _ => ?_
  rw [smul_eq_C_mul, map_mul, cc_subst ha, lg_cc h, mul_zero]

theorem formalAdd_constantCoeff (h : RLaw X V) {τ : Type} {a b : κ → MvPowerSeries τ C}
    (ha : ∀ s, constantCoeff (a s) = 0) (hb : ∀ s, constantCoeff (b s) = 0) (x : κ) :
    constantCoeff (addP X a b x) = 0 := by
  unfold addP
  rw [cc_subst (sum_cc h ha hb), h.exc]

theorem constantCoeff_expMulLog (h : RLaw X V) (M : Matrix κ κ C) {τ : Type} {a : κ → MvPowerSeries τ C}
    (ha : ∀ s, constantCoeff (a s) = 0) (x : κ) : constantCoeff (endP X M a x) = 0 := by
  unfold endP
  rw [cc_subst (lin_cc h M ha), h.exc]

theorem hAt_cc (h : RLaw X V) {τ : Type} {a b : κ → MvPowerSeries τ C}
    (ha : ∀ s, constantCoeff (a s) = 0) (hb : ∀ s, constantCoeff (b s) = 0) :
    constantCoeff (hAt X a b) = 0 := by
  unfold hAt
  rw [cc_subst (pair_cc ha hb), h_cc h]

theorem subst_addP (h : RLaw X V) {τ ρ : Type} [Finite τ] {a b : κ → MvPowerSeries τ C}
    (ha : ∀ s, constantCoeff (a s) = 0) (hb : ∀ s, constantCoeff (b s) = 0)
    {c : τ → MvPowerSeries ρ C} (hc : ∀ s, constantCoeff (c s) = 0) (x : κ) :
    subst c (addP X a b x) = addP X (fun y => subst c (a y)) (fun y => subst c (b y)) x := by
  have hS := hasSubst_of_constantCoeff_zero hc
  unfold addP
  rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero (sum_cc h ha hb)) hS]
  congr 1
  funext y
  rw [subst_add hS, subst_comp_subst_apply (hasSubst_of_constantCoeff_zero ha) hS,
    subst_comp_subst_apply (hasSubst_of_constantCoeff_zero hb) hS]

theorem subst_hAt {τ ρ : Type} [Finite τ] {a b : κ → MvPowerSeries τ C}
    (ha : ∀ s, constantCoeff (a s) = 0) (hb : ∀ s, constantCoeff (b s) = 0)
    {c : τ → MvPowerSeries ρ C} (hc : ∀ s, constantCoeff (c s) = 0) :
    subst c (hAt X a b) = hAt X (fun y => subst c (a y)) (fun y => subst c (b y)) := by
  have hS := hasSubst_of_constantCoeff_zero hc
  unfold hAt
  rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero (pair_cc ha hb)) hS]
  congr 1
  funext p
  split_ifs <;> rfl

theorem subst_endP_X (h : RLaw X V) (M : Matrix κ κ C) {ρ : Type}
    {c : κ → MvPowerSeries ρ C} (hc : ∀ s, constantCoeff (c s) = 0) (x : κ) :
    subst c (endP X M (MvPowerSeries.X : κ → MvPowerSeries κ C) x) = endP X M c x := by
  have hS := hasSubst_of_constantCoeff_zero hc
  unfold endP
  rw [subst_comp_subst_apply
    (hasSubst_of_constantCoeff_zero (lin_cc h M (fun s => constantCoeff_X s))) hS]
  congr 1
  funext y
  rw [← coe_substAlgHom hS, map_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [coe_substAlgHom hS, subst_smul hS, subst_self]
  rfl

theorem lg_endP (h : RLaw X V) (M : Matrix κ κ C) {τ : Type} {a : κ → MvPowerSeries τ C}
    (ha : ∀ s, constantCoeff (a s) = 0) (i : κ) :
    subst (endP X M a) (X.lg i) = ∑ y, M i y • subst a (X.lg y) := by
  have hS := hasSubst_of_constantCoeff_zero (lin_cc h M ha)
  have := subst_comp_subst_apply (hasSubst_of_constantCoeff_zero h.exc) hS (X.lg i)
  rw [h.lgex, subst_X hS] at this
  exact this.symm

theorem matrixEnd_add (h : RLaw X V) (M N : Matrix κ κ C) {τ : Type} {a : κ → MvPowerSeries τ C}
    (ha : ∀ s, constantCoeff (a s) = 0) : endP X (M + N) a = addP X (endP X M a) (endP X N a) := by
  funext i
  unfold addP
  simp only [lg_endP h _ ha]
  unfold endP
  simp only [Matrix.add_apply, add_smul, Finset.sum_add_distrib]

theorem formalAdd_integral (h : RLaw X V) {τ : Type} {a b : κ → MvPowerSeries τ C}
    (ha : ∀ s, constantCoeff (a s) = 0) (hb : ∀ s, constantCoeff (b s) = 0)
    (hai : ∀ s, IntS V (a s)) (hbi : ∀ s, IntS V (b s)) (x : κ) : IntS V (addP X a b x) := by
  have hc := pair_cc ha hb
  have hS := hasSubst_of_constantCoeff_zero hc
  have h1 := intS_subst hc (fun p => by split_ifs; exacts [hai _, hbi _]) (h.addInt x)
  rw [subst_addP h (gp_cc 0) (gp_cc 1) hc] at h1
  simpa [gp, subst_X hS] using h1

theorem defects [CharZero C] (h : RLaw X V) {τ : Type} {a b c : κ → MvPowerSeries τ C}
    (ha : ∀ s, constantCoeff (a s) = 0) (hb : ∀ s, constantCoeff (b s) = 0) (hc : ∀ s, constantCoeff (c s) = 0)
    (hai : ∀ s, IntS V (a s)) (hbi : ∀ s, IntS V (b s)) (hci : ∀ s, IntS V (c s)) :
    hAt X a c + hAt X b c - hAt X (addP X a b) c ∈ logInt V τ ∧
      hAt X a b + hAt X a c - hAt X a (addP X b c) ∈ logInt V τ := by
  let e : Fin 3 × κ → MvPowerSeries τ C := fun p => (![a, b, c] : Fin 3 → κ → MvPowerSeries τ C) p.1 p.2
  have he : ∀ p, constantCoeff (e p) = 0 := by
    rintro ⟨j, x⟩
    fin_cases j
    exacts [ha x, hb x, hc x]
  have hei : ∀ p, IntS V (e p) := by
    rintro ⟨j, x⟩
    fin_cases j
    exacts [hai x, hbi x, hci x]
  have hS := hasSubst_of_constantCoeff_zero he
  have s0 : (fun x => subst e (gp C κ (0 : Fin 3) x)) = a := funext fun x => subst_X hS _
  have s1 : (fun x => subst e (gp C κ (1 : Fin 3) x)) = b := funext fun x => subst_X hS _
  have s2 : (fun x => subst e (gp C κ (2 : Fin 3) x)) = c := funext fun x => subst_X hS _
  have g := fun j : Fin 3 => gp_cc (C := C) (κ := κ) j
  constructor
  · have h1 := logInt_subst he hei (mem_logInt.2 ⟨by
      rw [map_sub, map_add, hAt_cc h (g 0) (g 2), hAt_cc h (g 1) (g 2), hAt_cc h (formalAdd_constantCoeff h (g 0) (g 1)) (g 2)]
      simp, h.ph1⟩)
    rw [subst_sub hS, subst_add hS, subst_hAt (g 0) (g 2) he, subst_hAt (g 1) (g 2) he,
      subst_hAt (formalAdd_constantCoeff h (g 0) (g 1)) (g 2) he, funext (subst_addP h (g 0) (g 1) he), s0, s1, s2] at h1
    exact h1
  · have h1 := logInt_subst he hei (mem_logInt.2 ⟨by
      rw [map_sub, map_add, hAt_cc h (g 0) (g 1), hAt_cc h (g 0) (g 2), hAt_cc h (g 0) (formalAdd_constantCoeff h (g 1) (g 2))]
      simp, h.ph2⟩)
    rw [subst_sub hS, subst_add hS, subst_hAt (g 0) (g 1) he, subst_hAt (g 0) (g 2) he,
      subst_hAt (g 0) (formalAdd_constantCoeff h (g 1) (g 2)) he, funext (subst_addP h (g 1) (g 2) he), s0, s1, s2] at h1
    exact h1

theorem isEnd_add : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) (I : Fin 2 → Type) (κ : Type) [Fintype κ]
    (X : RawChart C d I κ), RLaw X V → ∀ M M' N N' : Matrix κ κ C,
      IsEnd X V M M' → IsEnd X V N N' → IsEnd X V (M + N) (M' + N') := by
  intro C _ V d I κ _ X h M M' N N' hM hN
  haveI := h.charZero
  have hX : ∀ s : κ, constantCoeff (MvPowerSeries.X s : MvPowerSeries κ C) = 0 := fun s => constantCoeff_X s
  refine ⟨fun i => ?_, fun i => ?_, ?_⟩
  · rw [matrixEnd_add h _ _ hX]
    exact formalAdd_integral h (constantCoeff_expMulLog h _ hX) (constantCoeff_expMulLog h _ hX) hM.1 hN.1 i
  · rw [matrixEnd_add h _ _ hX]
    exact formalAdd_integral h (constantCoeff_expMulLog h _ hX) (constantCoeff_expMulLog h _ hX) hM.2.1 hN.2.1 i
  have g := fun j : Fin 2 => gp_cc (C := C) (κ := κ) j
  have gi : ∀ (j : Fin 2) s, IntS V (gp C κ j s) := fun j s => intS_X _
  have ei : ∀ (A : Matrix κ κ C), (∀ i, IntS V (endP X A (MvPowerSeries.X : κ → MvPowerSeries κ C) i)) →
      ∀ (j : Fin 2) s, IntS V (endP X A (gp C κ j) s) := fun A hA j s => by
    rw [← subst_endP_X h A (g j)]
    exact intS_subst (g j) (gi j) (hA s)
  have ad : ∀ A A' : Matrix κ κ C, IsEnd X V A A' →
      hAt X (endP X A (gp C κ (0 : Fin 2))) (gp C κ 1) - hAt X (gp C κ 0) (endP X A' (gp C κ 1)) ∈
        logInt V (Fin 2 × κ) := fun A A' hA =>
    mem_logInt.2 ⟨by
      rw [map_sub, hAt_cc h (constantCoeff_expMulLog h _ (g 0)) (g 1), hAt_cc h (g 0) (constantCoeff_expMulLog h _ (g 1)), sub_zero], hA.2.2⟩
  have d1 := (defects h (constantCoeff_expMulLog h M (g 0)) (constantCoeff_expMulLog h N (g 0)) (g 1) (ei M hM.1 0) (ei N hN.1 0) (gi 1)).1
  have d2 := (defects h (g 0) (constantCoeff_expMulLog h M' (g 1)) (constantCoeff_expMulLog h N' (g 1)) (gi 0) (ei M' hM.2.1 1)
    (ei N' hN.2.1 1)).2
  have key := add_mem (sub_mem (add_mem (ad M M' hM) (ad N N' hN)) d1) d2
  rw [matrixEnd_add h M N (g 0), matrixEnd_add h M' N' (g 1)]
  convert (mem_logInt.1 key).2 using 2
  ring

end GlobalTheory.RowLaw.EndSum
