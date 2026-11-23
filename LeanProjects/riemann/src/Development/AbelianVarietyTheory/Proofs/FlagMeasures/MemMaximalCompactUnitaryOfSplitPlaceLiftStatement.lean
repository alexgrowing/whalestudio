import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemMaximalCompactUnitaryOfSplitPlaceLift
import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteCosetsHeckeSetAtSplitPlaceOutsideLevel
open NumberField IsDedekindDomain ReciprocityTheory.Aut
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_maximalCompactUnitary_of_splitPlaceLift : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : ReciprocityTheory.Aut.SplitPlace L) (g : ℕ), g.Prime → ((g : 𝓞 L) ∈ s.w.asIdeal) → ∀ (x : Formalism.AUTREP.GAf L n) (γ : GL (Fin n) (ZMod g)), GlobalTheory.LabPin.IsLift s x γ → x ∈ ReciprocityTheory.Aut.Umax L n := by
  first | exact @GlobalTheory.LiftInt.mem_Umax_of_isLift | exact GlobalTheory.LiftInt.mem_Umax_of_isLift | (intros; apply GlobalTheory.LiftInt.mem_Umax_of_isLift <;> assumption)
