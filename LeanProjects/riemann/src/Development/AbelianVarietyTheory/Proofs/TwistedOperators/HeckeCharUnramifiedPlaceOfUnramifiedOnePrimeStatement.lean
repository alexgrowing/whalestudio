import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeCharUnramifiedPlaceOfUnramifiedOnePrime
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsReading

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeChar_unramified_place_of_unramified_one_prime : ∀ (D : D7) (ν : (AE D)ˣ →* Circle), IsHeckeChar D ν → ResEta D ν 0 →
    ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : AF D.host.F), IsPlaceIdem D v ε →
    ∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v → GlobalTheory.LFun.UnrAt ν w → GlobalTheory.WeilParts.UnramAt ε ν := by
  first | exact @GlobalTheory.UnramFromOnePrime.unramAt_of_unrAt_one | exact GlobalTheory.UnramFromOnePrime.unramAt_of_unrAt_one | (intros; apply GlobalTheory.UnramFromOnePrime.unramAt_of_unrAt_one <;> assumption)
