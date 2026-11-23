import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLifted
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord

open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.LogPair GlobalTheory.Cartier ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem GlobalTheory.LogDR.isExtD_extD : ∀ (K : Type) [Field K], IsExtD ℤ K (extD K) := by
  intro K _
  refine { mul := ?_, sq := ?_, alg := ?_ }
  ·
    intro x y
    rw [extD_apply, extD_apply, extD_apply, CechDR.dDR_mul, add_comm]
    rfl
  · intro x
    rw [extD_apply, extD_apply, CechDR.dDR_dDR]
  · intro a
    rw [extD_apply, CechDR.dDR_algebraMap]
