import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.VolGe
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointHeightDualAndLinearComb
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.VolBr.Pair

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

theorem loc_one_add (P : Pair p) (a b a' b' : ℤ) (i : P.L.B.ι) (j : P.A.B.ι) :
    P.loc (a + a') (b + b') 1 i j = P.loc a b 1 i j * P.loc a' b' 1 i j := by
  have h₁ : ((P.r i : X.functionFieldˣ) : X.functionField) ≠ 0 := (P.r i).ne_zero
  have h₂ : ((P.r' j : X.functionFieldˣ) : X.functionField) ≠ 0 := (P.r' j).ne_zero
  simp only [loc, one_mul, zpow_add₀ h₁, zpow_add₀ h₂]
  ring

theorem rep_tens : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p),
    ∀ (a b a' b' : ℤ) (M M' : HermLB p), P.Rep a b M → P.Rep a' b' M' →
      P.Rep (a + a') (b + b') (M.tens M') := by
  intro k _ X _ p P a b a' b' M M' ⟨ρ, hρ, hu, hn⟩ ⟨ρ', hρ', hu', hn'⟩
  have e (c : (M.tens M').B.ι) (i : P.L.B.ι) (j : P.A.B.ι) :
      (((ρ c.1 * ρ' c.2 : X.functionFieldˣ) : X.functionField) / P.loc (a + a') (b + b') 1 i j) =
        ((ρ c.1 : X.functionField) / P.loc a b 1 i j) * ((ρ' c.2 : X.functionField) / P.loc a' b' 1 i j) := by
    rw [loc_one_add, Units.val_mul]
    ring
  refine ⟨fun c => ρ c.1 * ρ' c.2, GlobalTheory.PtHtComb.isRatSec_tens hρ hρ', ?_, ?_⟩
  · intro x c i j hc hi hj
    rw [e]
    exact (hu x c.1 i j hc.1 hi hj).mul (hu' x c.2 i j hc.2 hi hj)
  · intro σ y c i j hc hi hj
    obtain ⟨hc₁, hc₂⟩ := mem_ptsIn_inf.1 hc
    have u₁ := hu _ c.1 i j (mem_ptsIn.1 hc₁) (mem_ptsIn.1 hi) (mem_ptsIn.1 hj)
    have u₂ := hu' _ c.2 i j (mem_ptsIn.1 hc₂) (mem_ptsIn.1 hi) (mem_ptsIn.1 hj)
    have n₁ := hn σ y c.1 i j hc₁ hi hj
    have n₂ := hn' σ y c.2 i j hc₂ hi hj
    have z₁ : ‖ratVal ((ρ c.1 : X.functionField) / P.loc a b 1 i j) y‖ ≠ 0 :=
      norm_ne_zero_iff.2 (ratVal_ne_zero u₁)
    have z₂ : ‖ratVal ((ρ' c.2 : X.functionField) / P.loc a' b' 1 i j) y‖ ≠ 0 :=
      norm_ne_zero_iff.2 (ratVal_ne_zero u₂)
    change Real.log ‖ratVal ((((ρ c.1 * ρ' c.2 : X.functionFieldˣ) : X.functionField)) /
        P.loc (a + a') (b + b') 1 i j) y‖ - ((M.φ σ).φ c.1 y + (M'.φ σ).φ c.2 y) / 2 = _
    rw [e, ratVal_mul u₁.regAt u₂.regAt, norm_mul, Real.log_mul z₁ z₂]
    push_cast
    linear_combination n₁ + n₂

end GlobalTheory.VolBr.Pair
