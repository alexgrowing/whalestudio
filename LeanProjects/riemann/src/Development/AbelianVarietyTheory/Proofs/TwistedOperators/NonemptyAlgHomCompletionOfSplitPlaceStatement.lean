import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonemptyAlgHomCompletionOfSplitPlace
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsReading

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_algHom_completion_of_split_place : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : AF D.host.F), IsPlaceIdem D v ε →
    ¬ GlobalTheory.WeilParts.NonSplitAt D v ε → Nonempty (D.host.E →ₐ[D.host.F] Fv D.host.F v) := by
  first | exact @GlobalTheory.SplitPlaceEmb.nonempty_algHom_of_not_nonSplitAt | exact GlobalTheory.SplitPlaceEmb.nonempty_algHom_of_not_nonSplitAt | (intros; apply GlobalTheory.SplitPlaceEmb.nonempty_algHom_of_not_nonSplitAt <;> assumption)
