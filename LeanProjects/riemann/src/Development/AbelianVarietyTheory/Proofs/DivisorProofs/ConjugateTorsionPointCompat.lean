import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocCharEqValZpow
open NumberField IsDedekindDomain GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.UnrEuler Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped nonZeroDivisors
open Formalism.L2.Host (aboveF)

namespace GlobalTheory.UnrEuler

theorem eulerProd_eq_of_param_eq_zero {K : Type} [Field K] [NumberField K]
    {T T' : Set (HeightOneSpectrum (𝓞 K))} {c : Fam K} (hT : T' ⊆ T) (h : ∀ w ∈ T, w ∉ T' → c w = 0) (s : ℂ) :
    eulerProd T' c s = eulerProd T c s := by
  have e1 := tprod_subtype T'ᶜ (fun w => locL c w s)
  have e2 := tprod_subtype Tᶜ (fun w => locL c w s)
  refine e1.trans (Eq.trans (tprod_congr fun w => ?_) e2.symm)
  by_cases h1 : w ∈ T'
  · rw [Set.mulIndicator_of_notMem (by simpa using h1), Set.mulIndicator_of_notMem (by simpa using hT h1)]
  · by_cases h2 : w ∈ T
    · rw [Set.mulIndicator_of_mem (by simpa using h1), Set.mulIndicator_of_notMem (by simpa using h2), locL,
        h w h2 h1, eulerFac_zero]
    · rw [Set.mulIndicator_of_mem (by simpa using h1), Set.mulIndicator_of_mem (by simpa using h2)]

theorem hasProd_Lv_charL_of_ramified {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (ν : Chr F E) (T S₀ : Set (Pl F)) (hT : S₀ ⊆ T)
    (h : ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) ∈ T → w.under (𝓞 F) ∉ S₀ → ¬ UnrAt ν w) (s : ℂ)
    (hs : 1 < s.re) : Converges (above E T) (charFam ν) s ∧
      HasProd (fun v : {v : Pl F // v ∉ T} => Lv (charFam ν) v.1 s) (charL ν S₀ s) := by
  have hb : Bounded (above E T) (charFam ν) 1 0 := fun w _ => by
    unfold charFam
    split_ifs
    · refine ⟨by simp, fun b hb => ?_⟩
      rw [Multiset.mem_singleton.1 hb, Real.rpow_zero]
      exact (norm_val ν w).le
    · simp
  have hc : Converges (above E T) (charFam ν) s := hb.converges (by simpa using hs)
  refine ⟨hc, ?_⟩
  have e : charL ν S₀ s = LS T (charFam ν) s :=
    eulerProd_eq_of_param_eq_zero (T := above E T) (T' := above E S₀) (fun w hw => hT hw) (fun w h1 h2 => if_neg (h w h1 h2)) s
  rw [e]
  exact hasProd_Lv hc

end GlobalTheory.UnrEuler
