import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StepSubmoduleRegularSections
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StepInclStepProj
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.FlagChi Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.step_submodule_regular_sections : ∀ (Z : Scheme.{0}) [IsIntegral Z] (N : ℕ) (A : Matrix (Fin N) (Fin N) Z.functionField) (l : Fin N) (L : LB Z) (r : L.ι → Z.functionFieldˣ), IsUnit A.det → (∀ z : Z, ∃ B : Matrix (Fin N) (Fin N) Z.functionField, B.BlockTriangular id ∧ (∀ a b, RegAt z ((A * B) a b)) ∧ UnitAt z (A * B).det ∧ ∀ c, z ∈ L.U c → UnitAt z (B l l * r c)) → ∀ (x : Z) (v : Fin N → Z.functionField), v ∈ stepSub A⁻¹ ((l : ℕ) + 1) → (∀ a, RegAt x (v a)) → ∀ c, x ∈ L.U c → RegAt x ((A⁻¹ *ᵥ v) l * r c) := by
  first | exact @GlobalTheory.FlagChi.coord_regular | exact GlobalTheory.FlagChi.coord_regular | (intros; apply GlobalTheory.FlagChi.coord_regular <;> assumption)
