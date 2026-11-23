import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicCharacterTrivialRatAndSplit
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_adelic_character_trivial_rat_and_split : ∀ (D : D7) (V : HSp D) (ν : GA D V →* Circle), Continuous ν → (∀ γ ∈ GQ V, ν γ = 1) → (∀ e, IsSplitIdem D e → ∀ g, SuppAt e V g → ν g = 1) → ∀ g, ν g = 1 := by
  first | exact @GlobalTheory.SplitCharTrivial.eq_one_of_rat_of_split | exact GlobalTheory.SplitCharTrivial.eq_one_of_rat_of_split | (intros; apply GlobalTheory.SplitCharTrivial.eq_one_of_rat_of_split <;> assumption)
