import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateCurvePointAdditionCompat
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocCharEqValZpow
open NumberField IsDedekindDomain GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.UnrEuler Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped nonZeroDivisors
open Formalism.L2.Host (aboveF)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idealVal_conj_inv : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ ν : Chr F E, (∀ x : (AF F)ˣ, ν (Units.map (algebraMap (AF F) (AE F E) : AF F →* AE F E) x) = 1) → ∀ 𝔠 : FractionalIdeal (𝓞 E)⁰ E, 𝔠 ≠ 0 → (∀ w : HeightOneSpectrum (𝓞 E), FractionalIdeal.count E w 𝔠 ≠ 0 → UnrAt ν w) → idealVal ν (conjI σ 𝔠) = (idealVal ν 𝔠)⁻¹ := by
  first | exact @GlobalTheory.UnrEuler.ConjVal.idealVal_conjI | exact GlobalTheory.UnrEuler.ConjVal.idealVal_conjI | (intros; apply GlobalTheory.UnrEuler.ConjVal.idealVal_conjI <;> assumption)
