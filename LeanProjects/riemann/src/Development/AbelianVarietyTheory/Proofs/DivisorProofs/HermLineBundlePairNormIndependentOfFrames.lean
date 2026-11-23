import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.VolGe
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.VolBr.NuEq

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {σ : k →+* ℂ}
  {y : CxPts p σ}

theorem ratVal_one' : ratVal (1 : X.functionField) y = 1 := by
  have h1 := unitAt_one (under y)
  have e := ratVal_mul (y := y) h1.regAt h1.regAt
  rw [mul_one] at e
  exact (mul_eq_left₀ (ratVal_ne_zero h1)).1 e.symm

theorem ratVal_inv' {f : X.functionField} (hf : UnitAt (under y) f) :
    ratVal f⁻¹ y = (ratVal f y)⁻¹ := by
  have e := ratVal_mul hf.regAt hf.inv.regAt
  rw [mul_inv_cancel₀ hf.ne_zero, ratVal_one'] at e
  exact eq_inv_of_mul_eq_one_right e.symm

theorem unitAt_pow {x : X} {u : X.functionField} (h : UnitAt x u) (m : ℕ) : UnitAt x (u ^ m) := by
  induction m with
  | zero => simpa using unitAt_one x
  | succ m ih => rw [pow_succ]; exact ih.mul h

theorem unitAt_zpow {x : X} {u : X.functionField} (h : UnitAt x u) (n : ℤ) : UnitAt x (u ^ n) := by
  cases n with
  | ofNat m => simpa using unitAt_pow h m
  | negSucc m => rw [zpow_negSucc]; exact (unitAt_pow h _).inv

theorem ratVal_pow' {u : X.functionField} (h : UnitAt (under y) u) (m : ℕ) :
    ratVal (u ^ m) y = ratVal u y ^ m := by
  induction m with
  | zero => simpa using ratVal_one'
  | succ m ih => rw [pow_succ, ratVal_mul (unitAt_pow h m).regAt h.regAt, ih, pow_succ]

theorem ratVal_zpow' {u : X.functionField} (h : UnitAt (under y) u) (n : ℤ) :
    ratVal (u ^ n) y = ratVal u y ^ n := by
  cases n with
  | ofNat m => simpa using ratVal_pow' h m
  | negSucc m => rw [zpow_negSucc, zpow_negSucc, ratVal_inv' (unitAt_pow h _), ratVal_pow' h]

end GlobalTheory.VolBr.NuEq

namespace GlobalTheory.VolBr

open NuEq in

theorem nu_eq : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p), ∀ (a b : ℤ) (f : X.functionField), f ∈ P.H a b → ∀ (σ : k →+* ℂ) (y : CxPts p σ) i j, y ∈ ptsIn p σ (P.L.B.U i) → y ∈ ptsIn p σ (P.A.B.U j) → P.nu a b σ y f = ‖ratVal (P.loc a b f i j) y‖ * Real.exp (-(a * (P.L.φ σ).φ i y + b * (P.A.φ σ).φ j y) / 2) := by
  intro k _ X _ p P a b f hf σ y i j hi hj
  have hi₀ : y ∈ ptsIn p σ (P.L.B.U (pick (P.L.φ σ).isLB y)) := mem_pick _ y
  have hj₀ : y ∈ ptsIn p σ (P.A.B.U (pick (P.A.φ σ).isLB y)) := mem_pick _ y
  have hii := mem_ptsIn_inf.2 ⟨hi, hi₀⟩
  have hjj := mem_ptsIn_inf.2 ⟨hj, hj₀⟩
  have gi := gen_mem (mem_ptsIn.1 hii)
  have gj := gen_mem (mem_ptsIn.1 hjj)
  have uG := unitAt_fnOf (mem_ptsIn.1 hii) gi (P.L.B.g i (pick (P.L.φ σ).isLB y))
  have uG' := unitAt_fnOf (mem_ptsIn.1 hjj) gj (P.A.B.g j (pick (P.A.φ σ).isLB y))
  have uGa := unitAt_zpow uG a
  have uGb := unitAt_zpow uG' b
  have hreg : RegAt (under y) (P.loc a b f (pick (P.L.φ σ).isLB y) (pick (P.A.φ σ).isLB y)) :=
    hf _ _ _ (mem_ptsIn.1 hi₀) (mem_ptsIn.1 hj₀)
  have hloc : P.loc a b f i j =
      ((fnOf _ gi (P.L.B.g i (pick (P.L.φ σ).isLB y) : Γ(X, _))) ^ a *
        (fnOf _ gj (P.A.B.g j (pick (P.A.φ σ).isLB y) : Γ(X, _))) ^ b) *
        P.loc a b f (pick (P.L.φ σ).isLB y) (pick (P.A.φ σ).isLB y) := by
    simp only [Pair.loc]
    rw [P.hr i _ gi, P.hr' j _ gj, mul_zpow, mul_zpow]
    ring
  have eG := ratVal_fnOf hii gi (P.L.B.g i (pick (P.L.φ σ).isLB y) : Γ(X, _))
  have eG' := ratVal_fnOf hjj gj (P.A.B.g j (pick (P.A.φ σ).isLB y) : Γ(X, _))
  have c0 : 0 < ‖CxPts.gv p σ P.L.B i (pick (P.L.φ σ).isLB y) y‖ :=
    norm_pos_iff.2 (by rw [CxPts.gv, ← eG]; exact ratVal_ne_zero uG)
  have c0' : 0 < ‖CxPts.gv p σ P.A.B j (pick (P.A.φ σ).isLB y) y‖ :=
    norm_pos_iff.2 (by rw [CxPts.gv, ← eG']; exact ratVal_ne_zero uG')
  rw [Pair.nu, hloc, ratVal_mul (uGa.mul uGb).regAt hreg, ratVal_mul uGa.regAt uGb.regAt,
    ratVal_zpow' uG, ratVal_zpow' uG', eG, eG', (P.L.φ σ).trans i _ y hi hi₀,
    (P.A.φ σ).trans j _ y hj hj₀, norm_mul, norm_mul, norm_zpow, norm_zpow]
  change _ = ‖CxPts.gv p σ P.L.B i _ y‖ ^ a * ‖CxPts.gv p σ P.A.B j _ y‖ ^ b * _ * _
  rw [← Real.rpow_intCast, ← Real.rpow_intCast, Real.rpow_def_of_pos c0, Real.rpow_def_of_pos c0',
    Real.log_pow, Real.log_pow]
  have key : ∀ (N u v s t : ℝ), N * Real.exp (-(a * (s - 2 * u) + b * (t - 2 * v)) / 2) =
      Real.exp (u * a) * Real.exp (v * b) * N * Real.exp (-(a * s + b * t) / 2) := by
    intro N u v s t
    rw [mul_comm (Real.exp (u * a) * Real.exp (v * b)) N, mul_assoc, ← Real.exp_add, ← Real.exp_add]
    congr 2
    ring
  push_cast
  exact key _ _ _ _ _

end GlobalTheory.VolBr
