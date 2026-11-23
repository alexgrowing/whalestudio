import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelStructureLiftNilpotent
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDetGen
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_structure_lift_nilpotent : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (N : ℕ), 1 ≤ N →
    ∀ (R : Type) [CommRing R] [Algebra ℂ R] (π : R →ₐ[ℂ] ℂ), (∀ x ∈ RingHom.ker π, IsNilpotent x) →
    ∀ (X' : Obj F 𝔠 (Sp R)) (X₀ : Obj F 𝔠 (Sp ℂ)) (i : X₀.A.left ⟶ X'.A.left),
      X₀.IsPullBy X' (spMap (π : R →+* ℂ)) i → X₀.Level N → Nonempty (X'.Level N) := by
  first | exact @GlobalTheory.RealMult.LevelLift.level_lift | exact GlobalTheory.RealMult.LevelLift.level_lift | (intros; apply GlobalTheory.RealMult.LevelLift.level_lift <;> assumption)
