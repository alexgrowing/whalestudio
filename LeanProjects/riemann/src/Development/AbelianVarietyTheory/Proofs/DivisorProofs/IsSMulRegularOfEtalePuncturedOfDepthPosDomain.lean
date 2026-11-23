import Mathlib
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.ModDepthGE
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.ExistsIsRegularAppendOfModDepthGE
open IsLocalRing TensorProduct Pointwise

namespace GlobalTheory

theorem isSMulRegular_of_etale_punctured_of_depth_pos_domain :
    ∀ (S : Type) [CommRing S] [IsLocalRing S] [IsNoetherianRing S] [IsDomain S] (A : Type)
      [CommRing A] [Algebra S A], ReciprocityTheory.CA.ModDepthGE S A 1 →
      (∀ (p : Ideal S) [p.IsPrime], p ≠ maximalIdeal S →
        Algebra.Etale (Localization.AtPrime p) (TensorProduct S (Localization.AtPrime p) A)) →
      ∀ s : S, s ≠ 0 → IsSMulRegular A s := by
  intro S _ _ _ _ A _ _ hdepth het f hf
  obtain ⟨rs, hlen, hmem, hreg⟩ := hdepth
  obtain ⟨w, hw⟩ : ∃ w, rs = [w] := List.length_eq_one_iff.mp hlen
  subst hw
  have hwm : w ∈ maximalIdeal S := hmem w (by simp)
  have hwr : IsSMulRegular A w := ((RingTheory.Sequence.isRegular_cons_iff A w []).mp hreg).1
  have hmax : maximalIdeal S ∉ associatedPrimes S A := ReciprocityTheory.CA.max_not_mem_ass_of_reg hwm hwr
  refine IsSMulRegular.of_right_eq_zero_of_smul fun a ha => ?_
  by_contra ha0
  obtain ⟨P, hP, hle⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing S a ha0
  have hfP : f ∈ P := hle (Submodule.mem_colon_singleton.mpr (by simpa using ha))
  obtain ⟨hPprime, b, hb⟩ := Submodule.isAssociatedPrime_iff.mp hP
  haveI := hPprime
  have hPm : P ≠ maximalIdeal S := fun h => hmax (h ▸ hP)
  haveI := het P hPm
  set L := Localization.AtPrime P
  haveI : Module.Flat L (TensorProduct S L A) := inferInstance
  have hfb : f • b = 0 := by
    have : f ∈ (⊥ : Submodule S A).colon {b} := hb ▸ hfP
    simpa using Submodule.mem_colon_singleton.mp this
  have hloc : IsLocalizedModule P.primeCompl (TensorProduct.mk S L A 1) :=
    (isLocalizedModule_iff_isBaseChange P.primeCompl L _).mpr (TensorProduct.isBaseChange S A L)
  have hfL : algebraMap S L f ≠ 0 := by
    intro h0
    apply hf
    exact (IsLocalization.injective L (Ideal.primeCompl_le_nonZeroDivisors P)) (by simpa using h0)
  have h1 : (1 : L) ⊗ₜ[S] b = 0 := by
    have : algebraMap S L f • ((1 : L) ⊗ₜ[S] b) = 0 := by
      rw [algebraMap_smul, ← TensorProduct.tmul_smul, hfb, TensorProduct.tmul_zero]
    have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := TensorProduct S L A)
      (mem_nonZeroDivisors_of_ne_zero hfL)
    exact hreg (show algebraMap S L f • ((1 : L) ⊗ₜ[S] b) = algebraMap S L f • 0 by rw [this, smul_zero])
  obtain ⟨t, ht⟩ := (IsLocalizedModule.eq_zero_iff P.primeCompl (TensorProduct.mk S L A 1)).mp h1
  have htP : (t : S) ∈ P := by
    have : (t : S) ∈ (⊥ : Submodule S A).colon {b} :=
      Submodule.mem_colon_singleton.mpr (by simpa [Submonoid.smul_def] using ht)
    exact hb ▸ this
  exact t.2 htP

end GlobalTheory
