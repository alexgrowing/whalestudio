import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelStructurePowerSplit
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitObj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsDPModel
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_structure_power_split : ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {S : Scheme.{0}} {X : Obj F 𝔠 S} {N N' : ℕ}, N ≠ 0 → N' ≠ 0 → ∀ ξ : X.Level (N * N'),
    (∃ β : X.Level N, ∀ i, β.pt i = ξ.pt i ^ N') ∧ ∃ β' : X.Level N', ∀ i, β'.pt i = ξ.pt i ^ N := by
  first | exact @GlobalTheory.RealMult.Obj.Level.exists_pow_levels | exact GlobalTheory.RealMult.Obj.Level.exists_pow_levels | (intros; apply GlobalTheory.RealMult.Obj.Level.exists_pow_levels <;> assumption)
