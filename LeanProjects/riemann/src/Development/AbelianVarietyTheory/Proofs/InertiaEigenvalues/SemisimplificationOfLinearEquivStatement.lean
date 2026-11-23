import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimplificationOfLinearEquiv
import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.SemisimplificationConstituents
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semisimplification_of_linear_equiv : ∀ {k Γ : Type} [Field k] [Group Γ] {W : Type} [AddCommGroup W] [Module k W] [FiniteDimensional k W] {W' : Type} [AddCommGroup W'] [Module k W'] [FiniteDimensional k W'] {V : Type} [AddCommGroup V] [Module k V] [FiniteDimensional k V] (s : Representation k Γ W) (s' : Representation k Γ W') (ρ : Representation k Γ V) (e : W ≃ₗ[k] W'), (∀ g v, e (s g v) = s' g (e v)) → GlobalTheory.IndefiniteRowSideFullHecke.SemisimplificationConstituents.IsSemisimplificationOf s' ρ → GlobalTheory.IndefiniteRowSideFullHecke.SemisimplificationConstituents.IsSemisimplificationOf s ρ := by
  first | exact @GlobalTheory.isSemisimplificationOf_of_equiv | exact GlobalTheory.isSemisimplificationOf_of_equiv | (intros; apply GlobalTheory.isSemisimplificationOf_of_equiv <;> assumption)
