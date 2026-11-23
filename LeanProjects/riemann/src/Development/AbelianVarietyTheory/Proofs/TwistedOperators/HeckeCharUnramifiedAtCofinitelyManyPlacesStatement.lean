import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeCharUnramifiedAtCofinitelyManyPlaces
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsReading

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeChar_unramified_at_cofinitely_many_places : ∀ (D : D7) (χ : (AE D)ˣ →* Circle), IsHeckeChar D χ →
    {w : HeightOneSpectrum (𝓞 D.host.E) | ¬ GlobalTheory.LFun.UnrAt χ w}.Finite := by
  first | exact @GlobalTheory.HeckeFinRam.finite_ramified | exact GlobalTheory.HeckeFinRam.finite_ramified | (intros; apply GlobalTheory.HeckeFinRam.finite_ramified <;> assumption)
