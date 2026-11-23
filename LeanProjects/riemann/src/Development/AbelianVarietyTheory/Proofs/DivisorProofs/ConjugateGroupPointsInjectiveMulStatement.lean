import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateGroupPointsInjectiveMul
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocCharEqValZpow
open NumberField IsDedekindDomain GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.UnrEuler Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped nonZeroDivisors
open Formalism.L2.Host (aboveF)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_l_function_ideal_euler_product : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (ν : Chr F E) (T : Set (Pl F)) (𝔞 : FractionalIdeal (𝓞 E)⁰ E), 𝔞 ≠ 0 → (∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) ∈ T → FractionalIdeal.count E w 𝔞 = 0) → ∀ s : ℂ, HasProd (fun v : {v : Pl F // v ∉ T} => ∏ w ∈ aboveF (L := E) F v.1, ((val ν w ^ FractionalIdeal.count E w 𝔞 : ℂˣ) : ℂ) * npow w (-(s * (FractionalIdeal.count E w 𝔞 : ℂ)))) (((idealVal ν 𝔞 : ℂˣ) : ℂ) * (nrm 𝔞 : ℂ) ^ (-s)) := by
  first | exact @GlobalTheory.UnrEuler.IdealPart.hasProd_idealPart | exact GlobalTheory.UnrEuler.IdealPart.hasProd_idealPart | (intros; apply GlobalTheory.UnrEuler.IdealPart.hasProd_idealPart <;> assumption)
