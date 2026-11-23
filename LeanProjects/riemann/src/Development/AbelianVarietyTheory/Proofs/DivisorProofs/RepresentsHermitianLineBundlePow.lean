import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.VolGe
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

namespace GlobalTheory.VolBr.Pair

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

theorem ratVal_one' {σ : k →+* ℂ} (y : CxPts p σ) : ratVal (1 : X.functionField) y = 1 := by
  have h1 := (unitAt_one (under y)).regAt
  have e := ratVal_mul (y := y) h1 h1
  rw [mul_one] at e
  have h0 := ratVal_ne_zero (y := y) (unitAt_one (under y))
  exact (mul_eq_left₀ h0).1 e.symm

theorem unitAt_pow' {x : X} {f : X.functionField} (h : UnitAt x f) (n : ℕ) : UnitAt x (f ^ n) := by
  induction n with
  | zero => simpa using unitAt_one x
  | succ n ih => rw [pow_succ]; exact ih.mul h

theorem ratVal_pow' {σ : k →+* ℂ} {y : CxPts p σ} {f : X.functionField} (h : UnitAt (under y) f)
    (n : ℕ) : ratVal (f ^ n) y = ratVal f y ^ n := by
  induction n with
  | zero => simpa using ratVal_one' y
  | succ n ih =>
    rw [pow_succ, ratVal_mul (unitAt_pow' h n).regAt h.regAt, ih, pow_succ]

theorem loc_mul (P : Pair p) (a b : ℤ) (n : ℕ) (i : P.L.B.ι) (j : P.A.B.ι) :
    P.loc ((n : ℤ) * a) ((n : ℤ) * b) 1 i j = P.loc a b 1 i j ^ n := by
  simp only [loc, one_mul, mul_pow, mul_comm (n : ℤ), zpow_mul, zpow_natCast]

end GlobalTheory.VolBr.Pair

theorem GlobalTheory.VolBr.Pair.rep_pow : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p), ∀ (a b : ℤ) (M : HermLB p) (n : ℕ), P.Rep a b M → P.Rep (n * a) (n * b) (M.pow n) := by
  intro k _ X _ p P a b M n ⟨ρ, hρ, hu, hn⟩
  refine ⟨fun c => ρ (c PUnit.unit) ^ n, ?_, ?_, ?_⟩
  · intro j j' h
    have h' : genericPoint X ∈ M.B.U (j PUnit.unit) ⊓ M.B.U (j' PUnit.unit) :=
      ⟨Set.mem_iInter.1 h.1 PUnit.unit, Set.mem_iInter.1 h.2 PUnit.unit⟩
    have e : (M.pow n).B.g j j' = res (X := X) (U := M.B.U (j PUnit.unit) ⊓ M.B.U (j' PUnit.unit))
        (V := (M.pow n).B.U j ⊓ (M.pow n).B.U j')
        (fun _ hx => ⟨Set.mem_iInter.1 hx.1 PUnit.unit, Set.mem_iInter.1 hx.2 PUnit.unit⟩)
        (M.B.g (j PUnit.unit) (j' PUnit.unit)) ^ (n : ℤ) := by
      change ∏ _k : PUnit, _ = _
      exact Fintype.prod_unique _
    rw [e, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hρ _ _ h', mul_pow]
    congr 1
    rw [show ((res (X := X) (U := M.B.U (j PUnit.unit) ⊓ M.B.U (j' PUnit.unit))
        (V := (M.pow n).B.U j ⊓ (M.pow n).B.U j')
        (fun _ hx => ⟨Set.mem_iInter.1 hx.1 PUnit.unit, Set.mem_iInter.1 hx.2 PUnit.unit⟩)
        (M.B.g (j PUnit.unit) (j' PUnit.unit)) ^ (n : ℤ) : (Γ(X, (M.pow n).B.U j ⊓ (M.pow n).B.U j'))ˣ) :
          Γ(X, (M.pow n).B.U j ⊓ (M.pow n).B.U j')) =
        ((res (X := X) (U := M.B.U (j PUnit.unit) ⊓ M.B.U (j' PUnit.unit))
        (V := (M.pow n).B.U j ⊓ (M.pow n).B.U j')
        (fun _ hx => ⟨Set.mem_iInter.1 hx.1 PUnit.unit, Set.mem_iInter.1 hx.2 PUnit.unit⟩)
        (M.B.g (j PUnit.unit) (j' PUnit.unit)) : (Γ(X, (M.pow n).B.U j ⊓ (M.pow n).B.U j'))ˣ) :
          Γ(X, (M.pow n).B.U j ⊓ (M.pow n).B.U j')) ^ n by
        rw [zpow_natCast, Units.val_pow_eq_pow_val], map_pow]
    congr 1
    exact (fnOf_resG (fun _ hx => ⟨Set.mem_iInter.1 hx.1 PUnit.unit, Set.mem_iInter.1 hx.2 PUnit.unit⟩ :
      (M.pow n).B.U j ⊓ (M.pow n).B.U j' ≤ M.B.U (j PUnit.unit) ⊓ M.B.U (j' PUnit.unit)) h _).symm
  · intro x c i j hc hi hj
    rw [Pair.loc_mul, Units.val_pow_eq_pow_val, ← div_pow]
    exact Pair.unitAt_pow' (hu x (c PUnit.unit) i j (Set.mem_iInter.1 hc PUnit.unit) hi hj) n
  · intro σ y c i j hc hi hj
    have hc' := mem_pow_iff.1 hc
    have hU := hu _ (c PUnit.unit) i j (mem_ptsIn.1 hc') (mem_ptsIn.1 hi) (mem_ptsIn.1 hj)
    have e := hn σ y (c PUnit.unit) i j hc' hi hj
    rw [Pair.loc_mul, Units.val_pow_eq_pow_val, ← div_pow, Pair.ratVal_pow' hU, norm_pow,
      Real.log_pow]
    change _ - ((M.φ σ).zpow n).φ c y / 2 = _
    rw [show ((M.φ σ).zpow n).φ c y = (n : ℤ) * (M.φ σ).φ (c PUnit.unit) y from Weight.zpow_φ _ _ _ _]
    push_cast
    linear_combination (n : ℝ) * e
