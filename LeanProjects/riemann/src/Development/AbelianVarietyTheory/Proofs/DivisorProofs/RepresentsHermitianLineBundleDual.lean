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
namespace GlobalTheory.VolBr.Pair

theorem isRatSec_dual_of_inv {X : Scheme.{0}} [IsIntegral X] {L : LB X} {r : L.ι → X.functionFieldˣ}
    (hr : IsRatSec L r) : IsRatSec (CechPic.dual L) fun i => (r i)⁻¹ := fun i j hij => by
  have e : fnOf _ hij ((CechPic.dual L).g i j : Γ(X, L.U i ⊓ L.U j)ˣ).val =
      (fnOf _ hij (L.g i j : Γ(X, L.U i ⊓ L.U j)))⁻¹ := map_units_inv _ _
  rw [e, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, hr i j hij, mul_inv]
  rfl

theorem dual_quot_eq {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} (P : Pair p)
    (a b : ℤ) (u : X.functionField) (i : P.L.B.ι) (j : P.A.B.ι) :
    u⁻¹ / P.loc (-a) (-b) 1 i j = (u / P.loc a b 1 i j)⁻¹ := by
  simp only [loc, one_mul, zpow_neg, div_eq_mul_inv, mul_inv, inv_inv]

theorem ratVal_inv_unit {k : Type} [CommRing k] {σ : k →+* ℂ} {Z : Scheme.{0}} [IsIntegral Z]
    {q : Z ⟶ Sp k} {y : CxPts q σ} {f : Z.functionField} (hf : UnitAt (under y) f) :
    ratVal f⁻¹ y = (ratVal f y)⁻¹ := by
  have e := ratVal_mul (y := y) hf.regAt hf.inv.regAt
  have e1 := ratVal_fnOf (y := y) CxPts.mem_ptsIn_top trivial 1
  rw [map_one, CxPts.ev_one CxPts.mem_ptsIn_top] at e1
  rw [mul_inv_cancel₀ hf.ne_zero, e1] at e
  exact eq_inv_of_mul_eq_one_right e.symm

theorem rep_dual : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p),
    ∀ (a b : ℤ) (M : HermLB p), P.Rep a b M → P.Rep (-a) (-b) M.dual := by
  intro k _ X _ p P a b M ⟨ρ, hρ, hu, hn⟩
  refine ⟨fun c => (ρ c)⁻¹, isRatSec_dual_of_inv hρ, ?_, ?_⟩
  · intro x c i j hc hi hj
    rw [Units.val_inv_eq_inv_val, dual_quot_eq]
    exact (hu x c i j hc hi hj).inv
  · intro σ y c i j hc hi hj
    have hU := hu _ c i j (mem_ptsIn.1 hc) (mem_ptsIn.1 hi) (mem_ptsIn.1 hj)
    have e := hn σ y c i j hc hi hj
    rw [Units.val_inv_eq_inv_val, dual_quot_eq, ratVal_inv_unit hU, norm_inv, Real.log_inv]
    change _ - (-(M.φ σ).φ c y) / 2 = _
    push_cast
    linarith

end GlobalTheory.VolBr.Pair
