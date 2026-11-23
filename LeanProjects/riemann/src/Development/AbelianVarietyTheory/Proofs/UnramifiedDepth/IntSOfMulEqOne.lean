import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.NondegenerateCharts
import Formalism.LocalToGlobal.CharacterGerms.RowTieSelf
import Formalism.LocalToGlobal.CharacterGerms.BlockAdmissibleChart
import Formalism.LocalToGlobal.CharacterGerms.NegMem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CocycleIntegral
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.CalcExp

noncomputable section

open scoped BigOperators
open Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds GlobalTheory.RowLaw GlobalTheory.GaugeCocycle ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab

namespace GlobalTheory.RowVal

open MvPowerSeries

variable {C : Type} [Field C]

theorem mvExp_eq_subst [CharZero C] {σ : Type} {F : MvPowerSeries σ C} (hF : constantCoeff F = 0) :
    mvExp F = PowerSeries.subst F (PowerSeries.exp C) := by
  classical
  ext m
  have hS : PowerSeries.HasSubst F := PowerSeries.HasSubst.of_constantCoeff_zero hF
  rw [PowerSeries.coeff_subst hS, finsum_eq_sum_of_support_subset (s := Finset.range (m.degree + 1))]
  · show (∑ k ∈ Finset.range (m.degree + 1), coeff m (F ^ k) / (k.factorial : C)) = _
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [PowerSeries.coeff_exp, smul_eq_mul]
    simp [div_eq_mul_inv, mul_comm]
  · intro k hk
    rw [Function.mem_support] at hk
    by_contra hk'
    apply hk
    have h1 : m.degree < k := by simpa using hk'
    have h0 : coeff m (F ^ k) = 0 := by
      apply MvPowerSeries.coeff_of_lt_order
      refine lt_of_lt_of_le ?_ (MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero k hF)
      exact_mod_cast h1
    rw [h0, smul_zero]

theorem mvExp_add [CharZero C] {σ : Type} {F G : MvPowerSeries σ C} (hF : constantCoeff F = 0)
    (hG : constantCoeff G = 0) : mvExp (F + G) = mvExp F * mvExp G := by
  rw [mvExp_eq_subst hF, mvExp_eq_subst hG, mvExp_eq_subst (by rw [map_add, hF, hG, add_zero]),
    ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.exp_add hF hG]

theorem mvExp_zero' [CharZero C] {σ : Type} : mvExp (0 : MvPowerSeries σ C) = 1 := by
  rw [mvExp_eq_subst (map_zero _), ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.exp_zero]

theorem mvExp_sum [CharZero C] {σ α : Type} (s : Finset α) {F : α → MvPowerSeries σ C}
    (hF : ∀ i, constantCoeff (F i) = 0) : mvExp (∑ i ∈ s, F i) = ∏ i ∈ s, mvExp (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [mvExp_zero']
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, mvExp_add (hF a) (by simp [map_sum, hF]), ih]

theorem cc_subst {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ C} (ha : ∀ s, constantCoeff (a s) = 0)
    (F : MvPowerSeries σ C) : constantCoeff (subst a F) = constantCoeff F := by
  have hs := hasSubst_of_constantCoeff_zero ha
  have e : F = (F - MvPowerSeries.C (constantCoeff F)) + MvPowerSeries.C (constantCoeff F) := by ring
  rw [e, subst_add hs, map_add, constantCoeff_subst_zero ha (by simp), subst_C]
  simp

theorem subst_mvExp [CharZero C] {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ C}
    (ha : ∀ s, constantCoeff (a s) = 0) {F : MvPowerSeries σ C} (hF : constantCoeff F = 0) :
    subst a (mvExp F) = mvExp (subst a F) := by
  rw [mvExp_eq_subst hF, mvExp_eq_subst (by rw [cc_subst ha, hF]), ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.subst_exp a ha hF]

theorem intS_subst {V : VF C} {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ C}
    (ha : ∀ s, constantCoeff (a s) = 0) (hi : ∀ s, IntS V (a s)) {F : MvPowerSeries σ C} (hF : IntS V F) :
    IntS V (subst a F) :=
  (intS_iff_ig V _).2 (ig_subst (fun s => (intS_iff_ig V _).1 (hi s)) ha ((intS_iff_ig V _).1 hF))

theorem intS_X {V : VF C} {σ : Type} (s : σ) : IntS V (X s : MvPowerSeries σ C) :=
  (intS_iff_ig V _).2 (ig_X s)

theorem intS_one {V : VF C} {σ : Type} : IntS V (1 : MvPowerSeries σ C) :=
  (intS_iff_ig V _).2 (one_mem _)

theorem intS_zero {V : VF C} {σ : Type} : IntS V (0 : MvPowerSeries σ C) :=
  (intS_iff_ig V _).2 (zero_mem _)

theorem intS_mul {V : VF C} {σ : Type} {F G : MvPowerSeries σ C} (hF : IntS V F) (hG : IntS V G) :
    IntS V (F * G) :=
  (intS_iff_ig V _).2 (mul_mem ((intS_iff_ig V _).1 hF) ((intS_iff_ig V _).1 hG))

theorem intS_prod {V : VF C} {σ α : Type} (s : Finset α) {F : α → MvPowerSeries σ C} (hF : ∀ i, IntS V (F i)) :
    IntS V (∏ i ∈ s, F i) :=
  (intS_iff_ig V _).2 (prod_mem fun i _ => (intS_iff_ig V _).1 (hF i))

theorem intS_of_mul_eq_one {V : VF C} {σ : Type} {F G : MvPowerSeries σ C} (hF : IntS V F)
    (h1 : constantCoeff F = 1) (hFG : F * G = 1) : IntS V G := by
  obtain ⟨U, hU⟩ := RingHom.mem_range.1 ((intS_iff_ig V _).1 hF)
  have hU1 : constantCoeff U = 1 := by
    apply Subtype.ext
    have e := congrArg constantCoeff hU
    rw [constantCoeff_map, h1] at e
    exact e
  have hinv : U * MvPowerSeries.invOfUnit U 1 = 1 := MvPowerSeries.mul_invOfUnit U 1 (by simp [hU1])
  have e : G = MvPowerSeries.map (algebraMap (valRing V) C) (MvPowerSeries.invOfUnit U 1) := by
    have h2 := congrArg (MvPowerSeries.map (σ := σ) (algebraMap (valRing V) C)) hinv
    rw [map_mul, map_one, hU] at h2
    calc G = G * (F * MvPowerSeries.map (algebraMap (valRing V) C) (MvPowerSeries.invOfUnit U 1)) := by
          rw [h2, mul_one]
      _ = _ := by rw [← mul_assoc, mul_comm G F, hFG, one_mul]
  rw [e]
  exact (intS_iff_ig V _).2 (ig_map _)

def logInt [CharZero C] (V : VF C) (σ : Type) : AddSubgroup (MvPowerSeries σ C) where
  carrier := {F | constantCoeff F = 0 ∧ IntS V (mvExp F)}
  zero_mem' := ⟨map_zero _, by rw [mvExp_zero']; exact intS_one⟩
  add_mem' := fun {F G} hF hG => ⟨by rw [map_add, hF.1, hG.1, add_zero], by
    rw [mvExp_add hF.1 hG.1]; exact intS_mul hF.2 hG.2⟩
  neg_mem' := fun {F} hF => ⟨by rw [map_neg, hF.1, neg_zero], by
    refine intS_of_mul_eq_one hF.2 ?_ ?_
    · rw [mvExp_eq_subst hF.1, ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.constantCoeff_exp hF.1]
    · rw [← mvExp_add hF.1 (by rw [map_neg, hF.1, neg_zero]), add_neg_cancel, mvExp_zero']⟩

theorem mem_logInt [CharZero C] {V : VF C} {σ : Type} {F : MvPowerSeries σ C} :
    F ∈ logInt V σ ↔ constantCoeff F = 0 ∧ IntS V (mvExp F) := Iff.rfl

theorem logInt_subst [CharZero C] {V : VF C} {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ C}
    (ha : ∀ s, constantCoeff (a s) = 0) (hi : ∀ s, IntS V (a s)) {F : MvPowerSeries σ C}
    (hF : F ∈ logInt V σ) : subst a F ∈ logInt V τ :=
  ⟨by rw [cc_subst ha, hF.1], by rw [← subst_mvExp ha hF.1]; exact intS_subst ha hi hF.2⟩

variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ]

def IntEnd (X : RawChart C d I κ) (V : VF C) (A : Matrix κ κ C) : Prop :=
  ∀ i, IntS V (endP X A (MvPowerSeries.X : κ → MvPowerSeries κ C) i)

def hEnd (X : RawChart C d I κ) (A B : Matrix κ κ C) : MvPowerSeries κ C :=
  hAt X (endP X A (MvPowerSeries.X : κ → MvPowerSeries κ C)) (endP X B (MvPowerSeries.X : κ → MvPowerSeries κ C))

end GlobalTheory.RowVal
