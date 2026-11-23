import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharOfLowerRightBlockDetEventuallyEqOne
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTypeGroupBlockLift
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ValLeOneOfMemKO
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.charOfLowerRightBlockDet_eventually_eq_one : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (χ : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar χ → ∃ U : Set (GL (Fin (r + t)) k), IsOpen U ∧ (1 : GL (Fin (r + t)) k) ∈ U ∧ ∀ g ∈ U, GlobalTheory.BlockType.blockChar χ g = 1 := by
  first | exact @GlobalTheory.BlockType.blockChar_eventually_one | exact GlobalTheory.BlockType.blockChar_eventually_one | (intros; apply GlobalTheory.BlockType.blockChar_eventually_one <;> assumption)
