import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealLineOneParameterHomomorphism
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocCharEqValZpow
open NumberField IsDedekindDomain GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.UnrEuler Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped nonZeroDivisors
open Formalism.L2.Host (aboveF)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idealVal_different_eq_one : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], Algebra.Unramified (𝓞 F) (𝓞 E) → ∀ ν : Chr F E, (∀ x : (AF F)ˣ, ν (Units.map (algebraMap (AF F) (AE F E) : AF F →* AE F E) x) = 1) → (∀ w : HeightOneSpectrum (𝓞 E), FractionalIdeal.count E w (diffE E) ≠ 0 → UnrAt ν w) → idealVal ν (diffE E) = 1 := by
  first | exact @GlobalTheory.UnrEuler.idealVal_diffE | exact GlobalTheory.UnrEuler.idealVal_diffE | (intros; apply GlobalTheory.UnrEuler.idealVal_diffE <;> assumption)
