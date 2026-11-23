import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharpolyEqOfSemisimplification
import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.SemisimplificationConstituents
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.charpoly_eq_of_semisimplification : ∀ {k Γ : Type} [Field k] [Group Γ] {W : Type} [AddCommGroup W] [Module k W] [FiniteDimensional k W] {V : Type} [AddCommGroup V] [Module k V] [FiniteDimensional k V] (s : Representation k Γ W) (ρ : Representation k Γ V), GlobalTheory.IndefiniteRowSideFullHecke.SemisimplificationConstituents.IsSemisimplificationOf s ρ → ∀ g, LinearMap.charpoly (s g) = LinearMap.charpoly (ρ g) := by
  first | exact @GlobalTheory.SemisimplificationCharpoly.charpoly_eq | exact GlobalTheory.SemisimplificationCharpoly.charpoly_eq | (intros; apply GlobalTheory.SemisimplificationCharpoly.charpoly_eq <;> assumption)
