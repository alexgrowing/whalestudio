import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundlePairNormIndependentOfFrames
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSNef

theorem le_iff_local : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k), ∀ A B : HermLB p, Le B A ↔ ∃ (r : A.B.ι → X.functionFieldˣ) (r' : B.B.ι → X.functionFieldˣ), IsRatSec A.B r ∧ IsRatSec B.B r' ∧ (∀ (x : X) i j, x ∈ A.B.U i → x ∈ B.B.U j → RegAt x ((r i : X.functionField) / (r' j : X.functionField))) ∧ ∀ (σ : k →+* ℂ) (y : CxPts p σ) i j, y ∈ ptsIn p σ (A.B.U i) → y ∈ ptsIn p σ (B.B.U j) → ‖ratVal ((r i : X.functionField) / (r' j : X.functionField)) y‖ * Real.exp (-((A.φ σ).φ i y - (B.φ σ).φ j y) / 2) ≤ 1 := by
  intro k _ X _ p A B
  have hloc : ∀ (P : Pair p) i j, P.loc 1 (-1) 1 i j = (P.r i : X.functionField) / (P.r' j : X.functionField) := by
    intro P i j
    simp [Pair.loc, div_eq_mul_inv]
  have hexp : ∀ s t : ℝ, -(((1 : ℤ) : ℝ) * s + ((-1 : ℤ) : ℝ) * t) / 2 = -(s - t) / 2 := by
    intro s t
    push_cast
    ring
  constructor
  · rintro ⟨P, rfl, rfl, hH, hnu⟩
    refine ⟨P.r, P.r', P.hr, P.hr', fun x i j hi hj => ?_, fun σ y i j hi hj => ?_⟩
    · rw [← hloc]
      exact hH x i j hi hj
    · have e := hnu σ y
      rw [nu_eq k X p P 1 (-1) 1 hH σ y i j hi hj, hloc, hexp] at e
      exact e
  · rintro ⟨r, r', hr, hr', hreg, hnu⟩
    refine ⟨⟨A, B, r, r', hr, hr'⟩, rfl, rfl, fun x i j hi hj => ?_, fun σ y => ?_⟩
    · rw [hloc]
      exact hreg x i j hi hj
    · rw [Pair.nu, hloc, hexp]
      exact hnu σ y _ _ (mem_pick _ y) (mem_pick _ y)

end GlobalTheory.HSNef
