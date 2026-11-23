import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.VolGe
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

namespace GlobalTheory.VolBr.NuMul

theorem loc_mul {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} (P : Pair p)
    (a b a' b' : ℤ) (f g : X.functionField) (i : P.L.B.ι) (j : P.A.B.ι) :
    P.loc (a + a') (b + b') (f * g) i j = P.loc a b f i j * P.loc a' b' g i j := by
  have h1 : (P.r i : X.functionField) ≠ 0 := (P.r i).ne_zero
  have h2 : (P.r' j : X.functionField) ≠ 0 := (P.r' j).ne_zero
  simp only [Pair.loc, zpow_add₀ h1, zpow_add₀ h2]
  ring

theorem mul_mem_H_and_nu_mul : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p), ∀ (a b a' b' : ℤ) (f g : X.functionField), f ∈ P.H a b → g ∈ P.H a' b' → f * g ∈ P.H (a + a') (b + b') ∧ ∀ (σ : k →+* ℂ) (y : CxPts p σ), P.nu (a + a') (b + b') σ y (f * g) = P.nu a b σ y f * P.nu a' b' σ y g := by
  intro k _ X _ p P a b a' b' f g hf hg
  refine ⟨fun x i j hi hj => ?_, fun σ y => ?_⟩
  · rw [loc_mul]
    exact (hf x i j hi hj).mul (hg x i j hi hj)
  · have hi := mem_ptsIn.1 (mem_pick (P.L.φ σ).isLB y)
    have hj := mem_ptsIn.1 (mem_pick (P.A.φ σ).isLB y)
    simp only [Pair.nu]
    rw [loc_mul, ratVal_mul (hf _ _ _ hi hj) (hg _ _ _ hi hj), norm_mul]
    have e : -(((a + a' : ℤ) : ℝ) * (P.L.φ σ).φ (pick (P.L.φ σ).isLB y) y + ((b + b' : ℤ) : ℝ) * (P.A.φ σ).φ (pick (P.A.φ σ).isLB y) y) / 2
      = -((a : ℝ) * (P.L.φ σ).φ (pick (P.L.φ σ).isLB y) y + (b : ℝ) * (P.A.φ σ).φ (pick (P.A.φ σ).isLB y) y) / 2
        + -((a' : ℝ) * (P.L.φ σ).φ (pick (P.L.φ σ).isLB y) y + (b' : ℝ) * (P.A.φ σ).φ (pick (P.A.φ σ).isLB y) y) / 2 := by
      push_cast; ring
    rw [e, Real.exp_add]
    ring

end GlobalTheory.VolBr.NuMul
