import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeOfPrincipalMaximalIdealOfKerSmulLeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizationMaximalIdealEqSpanNilpotentArtinianStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizedModuleMemAnnSpanSmulTopStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerSmulLeIdealSmulOfFreeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalUniformiserAbovePrimeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsReducedFieldTensorIntFiniteReducedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsReducedQuotTensorOfReducedModPStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnnihilatorLiftOfMulEqPStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteOfSurjectiveTensorSemilinearStatement
open NumberField
open scoped TensorProduct

namespace GlobalTheory.FlatLift

theorem projective_of_nilpotent_of_reduced_quotient (D : Type) [CommRing D] [IsArtinianRing D] (x : D) (hx : IsNilpotent x)
    (hr : IsReduced (D ⧸ Ideal.span {x})) (N : Type 1) [AddCommGroup N] [Module D N]
    [Module.Finite D N]
    (h : ∀ n : N, x • n = 0 → n ∈ Ideal.span {a : D | x * a = 0} • (⊤ : Submodule D N)) :
    Module.Projective D N := by
  have hflat : Module.Flat D N := by
    apply Module.flat_of_localized_maximal
    intro P _
    have hloc := GlobalTheory.T.localization_maximalIdeal_eq_span_nilpotent_artinian D x hx hr P
    have hann := GlobalTheory.T.localizedModule_mem_annSpan_smul_of_mem D P.primeCompl x N h
    haveI := GlobalTheory.T.free_of_principal_maximalIdeal_of_ker_smul_le' (Localization.AtPrime P) (algebraMap D _ x) hloc
      (LocalizedModule P.primeCompl N) inferInstance hann
    exact Module.Flat.trans D (Localization.AtPrime P) _
  haveI : Module.FinitePresentation D N := Module.finitePresentation_of_finite D N
  exact Module.Flat.projective_of_finitePresentation

theorem projective_reduction_of_flat_lift : ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [NumberField F] (Λ : Type) [CommRing Λ] (k : Type) [Field k] (π : Λ →+* k), Function.Surjective π → RingHom.ker π = Ideal.span {(p : Λ)} → (p : Λ) ^ 2 = 0 → (∀ x : Λ, (p : Λ) * x = 0 → x ∈ Ideal.span {(p : Λ)}) → ∀ (M : Type 1) [AddCommGroup M] [Module Λ M] [Module (Λ ⊗[ℤ] 𝓞 F) M] [IsScalarTower Λ (Λ ⊗[ℤ] 𝓞 F) M], Module.Finite Λ M → Module.Free Λ M → ∀ (N : Type 1) [AddCommGroup N] [Module (k ⊗[ℤ] 𝓞 F) N] (f : M →ₛₗ[(Algebra.TensorProduct.map π.toIntAlgHom (AlgHom.id ℤ (𝓞 F))).toRingHom] N), Function.Surjective f → (∀ m, f m = 0 → m ∈ (RingHom.ker π) • (⊤ : Submodule Λ M)) → Module.Projective (k ⊗[ℤ] 𝓞 F) N := by
  intro p _ F _ _ Λ _ k _ π hπ hker hp2 hann M _ _ _ _ hfin hfree N _ _ f hf hkerf
  have hpk : (p : k) = 0 := by
    have : (p : Λ) ∈ RingHom.ker π := by rw [hker]; exact Ideal.subset_span rfl
    simpa using this
  have hkerp := GlobalTheory.T.mem_span_smul_of_smul_eq_zero_of_free Λ (p : Λ) hann M hfree
  have hkerf' : ∀ m, f m = 0 → m ∈ Ideal.span {(p : Λ)} • (⊤ : Submodule Λ M) := by
    intro m hm; rw [← hker]; exact hkerf m hm
  obtain ⟨ϖ, z, hϖz, ⟨n0, hn0⟩, hred⟩ := GlobalTheory.T.exists_global_uniformizer_above_prime p F
  haveI : IsArtinianRing (k ⊗[ℤ] 𝓞 F) := IsArtinianRing.of_finite k (k ⊗[ℤ] 𝓞 F)
  haveI : Module.Finite (k ⊗[ℤ] 𝓞 F) N := GlobalTheory.T.finite_of_surjective_semilinear_tensor Λ k π (𝓞 F) M hfin N f hf
  have hnil : IsNilpotent ((1 : k) ⊗ₜ[ℤ] ϖ) := by
    refine ⟨n0, ?_⟩
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp hn0
    rw [Algebra.TensorProduct.tmul_pow, one_pow, ← hy, mul_comm, ← nsmul_eq_mul,
      TensorProduct.tmul_smul, TensorProduct.smul_tmul', nsmul_eq_mul, mul_one, hpk,
      TensorProduct.zero_tmul]
  have hfinQ : Finite (𝓞 F ⧸ Ideal.span {(p : 𝓞 F), ϖ}) := by
    have hne : Ideal.span {(p : 𝓞 F)} ≠ ⊥ := by
      simp [Ideal.span_singleton_eq_bot, (Fact.out : p.Prime).ne_zero]
    haveI : Finite (𝓞 F ⧸ Ideal.span {(p : 𝓞 F)}) := Ideal.finiteQuotientOfFreeOfNeBot _ hne
    exact Finite.of_surjective _ (Ideal.Quotient.factor_surjective
      (Ideal.span_mono (by simp : ({(p : 𝓞 F)} : Set (𝓞 F)) ⊆ {(p : 𝓞 F), ϖ})))
  have hredD := GlobalTheory.T.isReduced_quot_tensor_of_reduced_mod_p (𝓞 F) k p ϖ hpk (GlobalTheory.T.isReduced_field_tensor_int_finite_reduced _ k)
  have hannN := GlobalTheory.T.annihilator_lift_of_mul_eq_p_alt p (𝓞 F) Λ k π hpk hp2 M hkerp N f hf hkerf' ϖ z hϖz
  exact projective_of_nilpotent_of_reduced_quotient _ _ hnil hredD N hannN

end GlobalTheory.FlatLift
