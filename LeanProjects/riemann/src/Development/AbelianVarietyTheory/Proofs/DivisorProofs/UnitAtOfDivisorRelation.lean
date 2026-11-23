import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueLiesUnder
open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.Mean4O

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CombUnit

section Local

variable {X : Scheme.{0}} [IsIntegral X] {x : X}

theorem unitAt_pow {f : X.functionField} (h : UnitAt x f) (n : ℕ) : UnitAt x (f ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact unitAt_one x
  | succ n ih => rw [pow_succ]; exact ih.mul h

theorem unitAt_zpow {f : X.functionField} (h : UnitAt x f) (n : ℤ) : UnitAt x (f ^ n) := by
  obtain ⟨m, rfl | rfl⟩ := n.eq_nat_or_neg
  · rw [zpow_natCast]; exact unitAt_pow h m
  · rw [zpow_neg, zpow_natCast]; exact (unitAt_pow h m).inv

theorem unitAt_prod {ι : Type} (s : Finset ι) (f : ι → X.functionField)
    (h : ∀ i ∈ s, UnitAt x (f i)) : UnitAt x (∏ i ∈ s, f i) :=
  Finset.prod_induction _ _ (fun _ _ ha hb => ha.mul hb) (unitAt_one x) h

theorem isEqn_sum {ι : Type} (s : Finset ι) (D : ι → CartierDiv X) (b : ι → ℤ)
    (t : ι → X.functionFieldˣ) (h : ∀ i ∈ s, (D i).IsEqn x (t i)) :
    (∑ i ∈ s, b i • D i).IsEqn x (∏ i ∈ s, t i ^ b i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.prod_empty]; exact CartierDiv.isEqn_zero x
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    exact ((h a (Finset.mem_insert_self a s)).zsmul (b a)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

end Local

end GlobalTheory.CombUnit

open GlobalTheory.CombUnit in

theorem GlobalTheory.CombUnit.unitAt_quot_of_relation : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (ι : Type) [Fintype ι] (DM : Y.Dv) (D : ι → Y.Dv) (q : ℕ) (b : ι → ℤ) (x : Y.X) (fM : Y.Fn) (f : ι → Y.Fn), q • DM = ∑ i, b i • D i → DM.GeneratesAt x fM → (∀ i, (D i).GeneratesAt x (f i)) → UnitAt x (fM ^ q / ∏ i, f i ^ b i) := by
  intro F _ _ Y ι _ DM D q b x fM f hrel hM hD
  obtain ⟨tM, htM⟩ := DM.exists_isEqn x
  choose t ht using fun i => (D i).exists_isEqn x
  have uM := htM.generatesAt_iff.1 hM
  have ui : ∀ i, UnitAt x (f i * t i) := fun i => (ht i).generatesAt_iff.1 (hD i)
  have e1 : (q • DM).IsEqn x (tM ^ q) := htM.nsmul q
  have e2 : (q • DM).IsEqn x (∏ i, t i ^ b i) := hrel ▸ isEqn_sum Finset.univ D b t fun i _ => ht i
  have uq := e1.iff_unitAt.1 e2
  have key := ((unitAt_pow uM q).mul uq).mul
    (unitAt_prod Finset.univ _ fun i _ => unitAt_zpow (ui i) (b i)).inv
  convert key using 1
  have hT : (∏ i, ((t i : Y.Fn)) ^ b i) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ (t i).ne_zero
  have htq : ((tM : Y.Fn)) ^ q ≠ 0 := pow_ne_zero _ tM.ne_zero
  simp only [Units.val_pow_eq_pow_val, Units.coe_prod, Units.val_zpow_eq_zpow_val, mul_zpow,
    Finset.prod_mul_distrib, mul_pow]
  field_simp
