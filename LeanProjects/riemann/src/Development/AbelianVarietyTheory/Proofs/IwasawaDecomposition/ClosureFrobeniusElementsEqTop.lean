import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeNormOfKummer

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField Pointwise

namespace GlobalTheory.Mem.FieldsEx

theorem isFrob_conj {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    {v : HeightOneSpectrum (𝓞 K)} {σ : L ≃ₐ[K] L} (h : IsFrob L v σ) (τ : L ≃ₐ[K] L) :
    IsFrob L v (τ * σ * τ⁻¹) := by
  obtain ⟨P, hP, hl, h⟩ := (isFrob_iff L v σ).1 h
  exact (isFrob_iff L v _).2 ⟨τ • P, inferInstance, inferInstance, h.conj τ⟩

theorem isFrob_one_of_fix {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    {v : HeightOneSpectrum (𝓞 K)} {σ : L ≃ₐ[K] L} (h : IsFrob L v σ) (F : IntermediateField K L)
    [NumberField F] (hF : ∀ x ∈ F, σ x = x) : IsFrob F v 1 := by
  obtain ⟨P, hP, hl, h⟩ := h
  refine ⟨P.under (𝓞 F), inferInstance, inferInstance, fun x => ?_⟩
  rw [Ideal.under_def, Ideal.mem_comap, one_smul, map_sub, map_pow]
  have h1 : σ • algebraMap (𝓞 F) (𝓞 L) x = algebraMap (𝓞 F) (𝓞 L) x :=
    RingOfIntegers.ext (hF _ (x : F).2)
  have := h (algebraMap (𝓞 F) (𝓞 L) x)
  rwa [h1] at this

theorem closure_frob_eq_top : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] (S : Set (HeightOneSpectrum (𝓞 K))), S.Finite →
    (∀ (F : Type) [Field F] [NumberField F] [Algebra K F],
      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → IsFrob F v 1) → ∀ σ : F ≃ₐ[K] F, σ = 1) →
    Subgroup.closure {σ : L ≃ₐ[K] L | ∃ v : HeightOneSpectrum (𝓞 K), v ∉ S ∧ IsFrob L v σ} = ⊤ := by
  intro K L _ _ _ _ _ _ S _ h
  set H := Subgroup.closure {σ : L ≃ₐ[K] L | ∃ v : HeightOneSpectrum (𝓞 K), v ∉ S ∧ IsFrob L v σ} with hH
  have hn : H.Normal := by
    refine ⟨fun n hn g => ?_⟩
    induction hn using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨v, hv, hx⟩ := hx
      exact Subgroup.subset_closure ⟨v, hv, isFrob_conj hx g⟩
    | one => simp
    | mul x y _ _ hx hy =>
      have := H.mul_mem hx hy
      convert this using 1
      group
    | inv x _ hx =>
      have := H.inv_mem hx
      convert this using 1
      group
  let F := IntermediateField.fixedField H
  have : IsGalois K F := IsGalois.of_fixedField_normal_subgroup H
  have : NumberField F := NumberField.of_module_finite K F
  have h1 := h F fun v hv => by
    obtain ⟨σ, hσ⟩ := exists_isFrob L v
    exact isFrob_one_of_fix hσ F fun x hx =>
      (IntermediateField.mem_fixedField_iff _ _).1 hx σ (Subgroup.subset_closure ⟨v, hv, hσ⟩)
  refine eq_top_iff.2 fun τ _ => ?_
  rw [← IntermediateField.fixingSubgroup_fixedField H, IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  have h2 := τ.restrictNormal_commutes F ⟨x, hx⟩
  rw [h1 (τ.restrictNormal F)] at h2
  exact h2.symm

end GlobalTheory.Mem.FieldsEx
