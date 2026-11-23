import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocCharEqValZpow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeFinVac

open scoped TensorProduct NNReal Matrix nonZeroDivisors
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnrEuler

namespace GlobalTheory.UnrEuler

theorem locL_charFam_ne_zero {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (ν : Chr F E) (w : HeightOneSpectrum (𝓞 E)) {s : ℂ} (hs : 0 < s.re) : locL (charFam ν) w s ≠ 0 := by
  refine inv_ne_zero (eulerPoly_ne_zero fun b hb => ?_)
  have hb1 : ‖(b : ℂ)‖ = 1 := by
    unfold charFam at hb
    split_ifs at hb
    · rw [Multiset.mem_singleton.1 hb, norm_val]
    · simp at hb
  rw [norm_mul, hb1, one_mul, norm_npow]
  refine Real.rpow_lt_one_of_one_lt_of_neg ?_ (by simpa using hs)
  exact_mod_cast one_lt_absNorm w

theorem unrFac_ne_zero_of_re_pos {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (ν : Chr F E) (𝔞 : FractionalIdeal (𝓞 E)⁰ E) {s : ℂ} (hs : 0 < s.re) (v : HeightOneSpectrum (𝓞 F)) :
    unrFac ν 𝔞 s v ≠ 0 :=
  mul_ne_zero (Finset.prod_ne_zero_iff.2 fun w _ => mul_ne_zero (Units.ne_zero _) (npow_ne_zero w _))
    (Finset.prod_ne_zero_iff.2 fun w _ => locL_charFam_ne_zero ν w hs)

theorem unrFac_nu_nat_ne_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (B : Base F E)
    (X : Chars F E) (a a' : ℕ), X.IsGood B a a' → ∀ (𝔞 : FractionalIdeal (𝓞 E)⁰ E) (k : ℕ), 1 ≤ k → ∀ v, v ∉ X.T →
      unrFac X.ν 𝔞 (k : ℂ) v ≠ 0 := by
  intro F E _ _ _ _ _ B X a a' _ 𝔞 k hk v _
  refine unrFac_ne_zero_of_re_pos _ _ ?_ v
  rw [Complex.natCast_re]
  exact_mod_cast hk

end GlobalTheory.UnrEuler
