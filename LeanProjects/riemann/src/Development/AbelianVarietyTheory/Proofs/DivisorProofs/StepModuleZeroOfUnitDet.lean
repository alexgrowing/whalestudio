import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StepInclStepProj
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.FlagChi Matrix

namespace GlobalTheory.FlagChi

theorem isZero_stepMod_zero (Z : Scheme.{0}) [IsIntegral Z] (N : ℕ)
    (M : Matrix (Fin N) (Fin N) Z.functionField) (hM : IsUnit M.det) :
    Limits.IsZero (stepMod M 0) := by
  rw [Limits.IsZero.iff_id_eq_zero]
  ext V s : 3
  change s = 0
  refine sec_ext (eq_zero_of_genVec fun h => ?_)
  have hv : M *ᵥ genVec h (vec s) = 0 := funext fun k =>
    (vec_mem s h _ h : genVec h (vec s) ∈ stepSub M 0) k (Nat.zero_le _)
  have := congrArg (fun w => M⁻¹ *ᵥ w) hv
  simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hM] using this

end GlobalTheory.FlagChi
