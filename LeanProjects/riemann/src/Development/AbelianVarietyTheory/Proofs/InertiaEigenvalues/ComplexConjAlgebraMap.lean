import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsOrbitProd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormVLeOfFix
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAbelianTotallyRealExtPrescribedCompletionStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCmFieldLiftDisjointOfRealSolvableStatement

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.CuspRep GlobalTheory.FunExt

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.IndDataDown

theorem complexConj_algebraMap (K K' : Type) [Field K] [NumberField K] [IsCMField K] [Field K'] [NumberField K']
    [IsCMField K'] [Algebra K K'] (t : K) :
    IsCMField.complexConj K' (algebraMap K K' t) = algebraMap K K' (IsCMField.complexConj K t) := by
  let φ : K' →+* ℂ := Classical.choice (inferInstance : Nonempty _)
  apply φ.injective
  rw [IsCMField.complexEmbedding_complexConj, ← RingHom.comp_apply φ (algebraMap K K'),
    ← IsCMField.complexEmbedding_complexConj K (φ.comp (algebraMap K K')) t]
  rfl

theorem comap_conj_ne (K : Type) [Field K] [NumberField K] [IsCMField K] (x : HeightOneSpectrum (𝓞 K))
    (hx : GlobalTheory.UnitaryBC.IsSplitAt x) :
    x.asIdeal.comap ((IsCMField.ringOfIntegersComplexConj K : 𝓞 K ≃ₐ[𝓞 (maximalRealSubfield K)] 𝓞 K) :
      𝓞 K →+* 𝓞 K) ≠ x.asIdeal := by
  intro heq
  obtain ⟨u, hne, hu⟩ := hx
  set c := IsCMField.ringOfIntegersComplexConj K
  have hcc : ∀ a : 𝓞 K, c (c a) = a := fun a => by
    ext
    simp [c, IsCMField.complexConj_apply_apply]
  have hle : u.asIdeal ≤ x.asIdeal := by
    intro a ha
    have h1 : a * c a ∈ u.asIdeal := u.asIdeal.mul_mem_right _ ha
    have h2 : c (a * c a) = a * c a := by rw [map_mul, hcc, mul_comm]
    obtain ⟨y, hy⟩ := (IsCMField.ringOfIntegersComplexConj_eq_self_iff K _).1 h2
    have h3 : y ∈ (u.under (𝓞 (maximalRealSubfield K))).asIdeal := by
      show algebraMap _ _ y ∈ u.asIdeal
      rw [hy]; exact h1
    rw [hu] at h3
    have h4 : a * c a ∈ x.asIdeal := by
      have : algebraMap _ _ y ∈ x.asIdeal := h3
      rwa [hy] at this
    rcases x.isPrime.mem_or_mem h4 with h5 | h5
    · exact h5
    · rw [← heq]; exact h5
  exact hne (HeightOneSpectrum.ext (u.isMaximal.eq_of_le x.isPrime.ne_top hle))

theorem isSplitAt_of_under (K K' : Type) [Field K] [NumberField K] [IsCMField K] [Field K'] [NumberField K']
    [IsCMField K'] [Algebra K K'] (x : HeightOneSpectrum (𝓞 K)) (x' : HeightOneSpectrum (𝓞 K')) :
    x'.under (𝓞 K) = x → GlobalTheory.UnitaryBC.IsSplitAt x → GlobalTheory.UnitaryBC.IsSplitAt x' := by
  intro hxx hx
  set c := IsCMField.ringOfIntegersComplexConj K
  set c' := IsCMField.ringOfIntegersComplexConj K'
  have hcomm : ∀ a : 𝓞 K, c' (algebraMap (𝓞 K) (𝓞 K') a) = algebraMap (𝓞 K) (𝓞 K') (c a) := fun a => by
    ext
    exact complexConj_algebraMap K K' (a : K)
  haveI := x'.isPrime
  have hbot : x'.asIdeal.comap (c' : 𝓞 K' →+* 𝓞 K') ≠ ⊥ := by
    obtain ⟨b, hb, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot x'.ne_bot
    intro h0
    have : c'.symm b ∈ x'.asIdeal.comap (c' : 𝓞 K' →+* 𝓞 K') := by
      show c' (c'.symm b) ∈ x'.asIdeal
      rw [AlgEquiv.apply_symm_apply]; exact hb
    rw [h0, Ideal.mem_bot] at this
    exact hb0 (by simpa using congrArg c' this)
  refine ⟨⟨x'.asIdeal.comap (c' : 𝓞 K' →+* 𝓞 K'), Ideal.comap_isPrime _ _, hbot⟩, fun heq => ?_, ?_⟩
  · apply comap_conj_ne K x hx
    have heq' : x'.asIdeal.comap (c' : 𝓞 K' →+* 𝓞 K') = x'.asIdeal := congrArg HeightOneSpectrum.asIdeal heq
    ext a
    rw [← hxx]
    show algebraMap (𝓞 K) (𝓞 K') (c a) ∈ x'.asIdeal ↔ algebraMap (𝓞 K) (𝓞 K') a ∈ x'.asIdeal
    rw [← hcomm]
    exact Ideal.ext_iff.1 heq' _
  · ext b
    show c' (algebraMap _ _ b) ∈ x'.asIdeal ↔ algebraMap _ _ b ∈ x'.asIdeal
    rw [AlgEquiv.commutes]

end GlobalTheory.IndDataDown

namespace GlobalTheory.IndDataDown

end GlobalTheory.IndDataDown
