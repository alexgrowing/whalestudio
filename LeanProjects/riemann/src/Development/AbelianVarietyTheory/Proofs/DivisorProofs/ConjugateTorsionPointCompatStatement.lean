import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateTorsionPointCompat
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocCharEqValZpow
open NumberField IsDedekindDomain GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.UnrEuler Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped nonZeroDivisors
open Formalism.L2.Host (aboveF)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_l_function_euler_product_convergent : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (ν : Chr F E) (T S₀ : Set (Pl F)), S₀ ⊆ T → (∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) ∈ T → w.under (𝓞 F) ∉ S₀ → ¬ UnrAt ν w) → ∀ s : ℂ, 1 < s.re → Converges (above E T) (charFam ν) s ∧ HasProd (fun v : {v : Pl F // v ∉ T} => Lv (charFam ν) v.1 s) (charL ν S₀ s) := by
  first | exact @GlobalTheory.UnrEuler.hasProd_Lv_charL_of_ramified | exact GlobalTheory.UnrEuler.hasProd_Lv_charL_of_ramified | (intros; apply GlobalTheory.UnrEuler.hasProd_Lv_charL_of_ramified <;> assumption)
