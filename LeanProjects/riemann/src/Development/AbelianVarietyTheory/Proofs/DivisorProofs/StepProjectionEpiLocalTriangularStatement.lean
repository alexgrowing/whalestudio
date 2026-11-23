import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StepProjectionEpiLocalTriangular
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StepInclStepProj
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.FlagChi Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.step_projection_epi_local_triangular : ∀ (Z : Scheme.{0}) [IsIntegral Z] (N : ℕ) (A : Matrix (Fin N) (Fin N) Z.functionField) (l : Fin N) (L : LB Z) (r : L.ι → Z.functionFieldˣ) (hr : IsRatSec L r), L.IsLB → IsUnit A.det → (∀ z : Z, ∃ B : Matrix (Fin N) (Fin N) Z.functionField, B.BlockTriangular id ∧ (∀ a b, RegAt z ((A * B) a b)) ∧ UnitAt z (A * B).det ∧ ∀ c, z ∈ L.U c → UnitAt z (B l l * r c)) → Epi (stepProj A⁻¹ l hr) := by
  first | exact @GlobalTheory.FlagChi.epi_stepProj | exact GlobalTheory.FlagChi.epi_stepProj | (intros; apply GlobalTheory.FlagChi.epi_stepProj <;> assumption)
