import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalOrderCompletionSurjectiveFromIntegralAdeles
import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIdemOfAlgebraMap
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIntegralSplitIdempotentOverTwo
open IsDedekindDomain NumberField
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localOrderCompletion_surjective_from_integralAdeles : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (a : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v ⊗[F] E), a ∈ GlobalTheory.PlaceComp.ordAt E v → ∃ t ∈ GlobalTheory.PlaceComp.intA F E, GlobalTheory.PlaceComp.evF E v t = a := by
  first | exact @GlobalTheory.OrdLift.ordAt_lift | exact GlobalTheory.OrdLift.ordAt_lift | (intros; apply GlobalTheory.OrdLift.ordAt_lift <;> assumption)
