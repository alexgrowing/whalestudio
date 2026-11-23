import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicCharacterTrivialOfLocal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts
open scoped TensorProduct Kronecker ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryAdelicCharacter_trivial_of_local : ∀ (D : D7) (V : HSp D) (ν : GA D V →* Circle), Continuous ν → (∀ g ∈ GinfC V, ν g = 1) → (∀ e, IsSplitIdem D e → ∀ g, SuppAt e V g → ν g = 1) → (∀ v ε, NonSplitAt D v ε → ∀ g, SuppPl ε V g → ν g = 1) → ∀ g, ν g = 1 := by
  first | exact @GlobalTheory.LocalGlobalChar.eq_one_of_local | exact GlobalTheory.LocalGlobalChar.eq_one_of_local | (intros; apply GlobalTheory.LocalGlobalChar.eq_one_of_local <;> assumption)
