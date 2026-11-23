import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsHeckeCharacterOfClassGroup
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StandardOpenSubgroupLeKerInv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConductorEqTopOfStandardOpen
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InfiniteEmbeddingMemStandardOpenSubgroup
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DiscrNormConductorEqDFOfUnramified
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RootNumberEqDifferentCoeff
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModuleSectionMemStandardOpenSubgroup
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SumAddCharOfMulMulOfMulInv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FunctionalEquationOfUnramified

noncomputable section

open NumberField GroundTheory.Global GroundTheory.Global.IdeleGroup GlobalTheory.CompanionTheory.PartialZeta
open scoped nonZeroDivisors

namespace GlobalTheory.CompanionTheory.Hypotheses₂

variable {F : Type} [Field F] [NumberField F]

theorem coeff_inv_classHecke (ψ : AddChar (Additive (ClassGroup (𝓞 F))) ℂ) (J : (Ideal (𝓞 F))⁰) :
    ((classHecke ψ)⁻¹).coeff (J : Ideal (𝓞 F)) = ψ (Additive.ofMul (ClassGroup.mk0 J)⁻¹) := by
  have hJ : (J : Ideal (𝓞 F)) ≠ ⊥ := nonZeroDivisors.coe_ne_zero J
  have h1 := coeff_inv_mul_coeff F (classHecke ψ) (standardOpenSubgroup_le_ker ψ) J hJ
  rw [coeff_classHecke ψ J hJ] at h1
  have h2 : ψ (Additive.ofMul (ClassGroup.mk0 J)⁻¹) * ψ (Additive.ofMul (ClassGroup.mk0 J)) = 1 := by
    rw [← AddChar.map_add_eq_mul, ← ofMul_mul, inv_mul_cancel, ofMul_one, AddChar.map_zero_eq_one]
  exact mul_right_cancel₀ (right_ne_zero_of_mul_eq_one h2) (h1.trans h2.symm)

def zetaOfClass (C : ClassGroup (𝓞 F)) (s : ℂ) : ℂ :=
  ∑ ψ : AddChar (Additive (ClassGroup (𝓞 F))) ℂ,
    ((Fintype.card (ClassGroup (𝓞 F)) : ℂ)⁻¹ * ψ (Additive.ofMul C⁻¹)) * (classHecke ψ).continuedLFunction s

def zetaOfClassInv (C : ClassGroup (𝓞 F)) (s : ℂ) : ℂ :=
  ∑ ψ : AddChar (Additive (ClassGroup (𝓞 F))) ℂ,
    ((Fintype.card (ClassGroup (𝓞 F)) : ℂ)⁻¹ * ψ (Additive.ofMul C)) * ((classHecke ψ)⁻¹).continuedLFunction s

theorem isPartialZeta_of_indicator {ι : Type} [Fintype ι] (χ : ι → HeckeCharacter F) (c : ι → ℂ)
    (C : ClassGroup (𝓞 F)) (hU : ∀ i, standardOpenSubgroup F ≤ (χ i).toIdele.ker)
    (horth : ∀ J : (Ideal (𝓞 F))⁰,
      (ClassGroup.mk0 J = C → ∑ i, c i * (χ i).coeff (J : Ideal (𝓞 F)) = 1) ∧
      (ClassGroup.mk0 J ≠ C → ∑ i, c i * (χ i).coeff (J : Ideal (𝓞 F)) = 0)) :
    GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.IsPartialZeta C (fun s => ∑ i, c i * (χ i).continuedLFunction s) := by
  classical
  refine ⟨?_, fun s hs => ?_⟩
  · exact DifferentiableOn.fun_sum fun i _ => (differentiableOn_continuedLFunction F (χ i) (hU i)).const_mul (c i)
  · have h1 : HasSum (fun I : Ideal (𝓞 F) =>
        ∑ i, c i * ((χ i).coeff I * (Ideal.absNorm I : ℂ) ^ (-s)))
        (∑ i, c i * (χ i).continuedLFunction s) := by
      refine hasSum_sum fun i _ => ?_
      rw [(χ i).continuedLFunction_eq hs]
      exact ((χ i).hasSum_LFunction hs).mul_left (c i)
    have hfac : ∀ I : Ideal (𝓞 F),
        ∑ i, c i * ((χ i).coeff I * (Ideal.absNorm I : ℂ) ^ (-s)) =
          (∑ i, c i * (χ i).coeff I) * (Ideal.absNorm I : ℂ) ^ (-s) := fun I => by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => (mul_assoc _ _ _).symm
    let g : {J : (Ideal (𝓞 F))⁰ // ClassGroup.mk0 J = C} → Ideal (𝓞 F) :=
      fun J => (J.1 : Ideal (𝓞 F))
    have hg : Function.Injective g := fun a b hab =>
      Subtype.ext (Subtype.ext hab)
    have hsupp : ∀ I ∉ Set.range g,
        ∑ i, c i * ((χ i).coeff I * (Ideal.absNorm I : ℂ) ^ (-s)) = 0 := by
      intro I hI
      by_cases hbot : I = ⊥
      · subst hbot
        simp
      · let J : (Ideal (𝓞 F))⁰ := ⟨I, mem_nonZeroDivisors_of_ne_zero hbot⟩
        have hJ : ClassGroup.mk0 J ≠ C := fun h => hI ⟨⟨J, h⟩, rfl⟩
        rw [hfac, show I = (J : Ideal (𝓞 F)) from rfl, (horth J).2 hJ, zero_mul]
    have h2 := (hg.hasSum_iff hsupp).2 h1
    have h3 : (fun I : Ideal (𝓞 F) =>
        ∑ i, c i * ((χ i).coeff I * (Ideal.absNorm I : ℂ) ^ (-s))) ∘ g =
        fun J : {J : (Ideal (𝓞 F))⁰ // ClassGroup.mk0 J = C} =>
          ((Ideal.absNorm (J.1 : Ideal (𝓞 F)) : ℕ) : ℂ) ^ (-s) := funext fun J => by
      simp only [Function.comp_apply]
      rw [hfac, show g J = (J.1 : Ideal (𝓞 F)) from rfl, (horth J.1).1 J.2, one_mul]
    rw [h3] at h2
    exact h2

theorem card_classGroup_ne_zero : (Fintype.card (ClassGroup (𝓞 F)) : ℂ) ≠ 0 :=
  Nat.cast_ne_zero.2 Fintype.card_ne_zero

theorem isPartialZeta_zetaOfClass (C : ClassGroup (𝓞 F)) :
    GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.IsPartialZeta C (zetaOfClass C) := by
  classical
  refine isPartialZeta_of_indicator (fun ψ => classHecke ψ) _ C (fun ψ => standardOpenSubgroup_le_ker ψ) fun J => ?_
  have hJ : (J : Ideal (𝓞 F)) ≠ ⊥ := nonZeroDivisors.coe_ne_zero J
  have e : ∑ ψ : AddChar (Additive (ClassGroup (𝓞 F))) ℂ,
      ((Fintype.card (ClassGroup (𝓞 F)) : ℂ)⁻¹ * ψ (Additive.ofMul C⁻¹)) * (classHecke ψ).coeff (J : Ideal (𝓞 F)) =
      (Fintype.card (ClassGroup (𝓞 F)) : ℂ)⁻¹ * (if ClassGroup.mk0 J = C then (Fintype.card (ClassGroup (𝓞 F)) : ℂ) else 0) := by
    rw [← sum_addChar_ofMul_mul_ofMul_inv, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ψ _ => ?_
    rw [coeff_classHecke ψ J hJ]
    ring_nf
  rw [e]
  constructor
  · intro h
    rw [if_pos h, inv_mul_cancel₀ card_classGroup_ne_zero]
  · intro h
    rw [if_neg h, mul_zero]

theorem isPartialZeta_zetaOfClassInv (C : ClassGroup (𝓞 F)) :
    GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.IsPartialZeta C (zetaOfClassInv C) := by
  classical
  refine isPartialZeta_of_indicator (fun ψ => (classHecke ψ)⁻¹) _ C
    (fun ψ => standardOpenSubgroup_le_ker_inv F _ (standardOpenSubgroup_le_ker ψ)) fun J => ?_
  have e : ∑ ψ : AddChar (Additive (ClassGroup (𝓞 F))) ℂ,
      ((Fintype.card (ClassGroup (𝓞 F)) : ℂ)⁻¹ * ψ (Additive.ofMul C)) * ((classHecke ψ)⁻¹).coeff (J : Ideal (𝓞 F)) =
      (Fintype.card (ClassGroup (𝓞 F)) : ℂ)⁻¹ * (if C = ClassGroup.mk0 J then (Fintype.card (ClassGroup (𝓞 F)) : ℂ) else 0) := by
    rw [← sum_addChar_ofMul_mul_ofMul_inv, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ψ _ => ?_
    rw [coeff_inv_classHecke ψ J, mul_assoc]
  rw [e]
  constructor
  · intro h
    rw [if_pos h.symm, inv_mul_cancel₀ card_classGroup_ne_zero]
  · intro h
    rw [if_neg (Ne.symm h), mul_zero]

theorem functionalEquation_classHecke [IsTotallyReal F] (ψ : AddChar (Additive (ClassGroup (𝓞 F))) ℂ)
    (D : (Ideal (𝓞 F))⁰) (hD : (D : Ideal (𝓞 F)) = differentIdeal ℤ (𝓞 F))
    (s : ℂ) (h1 : ∀ n : ℕ, s ≠ -2 * n) (h2 : ∀ n : ℕ, 1 - s ≠ -2 * n) :
    (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.dF F : ℂ) ^ (s / 2) * Complex.Gammaℝ s ^ Module.finrank ℚ F * (classHecke ψ).continuedLFunction s =
      ψ (Additive.ofMul (ClassGroup.mk0 D)) * ((GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.dF F : ℂ) ^ ((1 - s) / 2) *
        Complex.Gammaℝ (1 - s) ^ Module.finrank ℚ F * ((classHecke ψ)⁻¹).continuedLFunction (1 - s)) := by
  have hU := standardOpenSubgroup_le_ker ψ
  have h := fe_of_parts F (classHecke ψ) (discrNormConductor_eq_dF_of_unramified F _ hU)
    (gammaFactor_eq_of_unramified F _ hU)
    (gammaFactor_eq_of_unramified F _ (standardOpenSubgroup_le_ker_inv F _ hU))
    (rootNumber_eq_coeff_different F _ hU) s h1 h2
  rw [← hD, coeff_classHecke ψ _ (nonZeroDivisors.coe_ne_zero D)] at h
  exact h

end GlobalTheory.CompanionTheory.Hypotheses₂

theorem GlobalTheory.CompanionTheory.Hypotheses₂.partialZetaFunctionalEquation : GlobalTheory.Published.PartialZetaFunctionalEquation := by
  intro F _ _ _ C C' D hD hC
  refine ⟨GlobalTheory.CompanionTheory.Hypotheses₂.zetaOfClass C, GlobalTheory.CompanionTheory.Hypotheses₂.zetaOfClassInv C',
    GlobalTheory.CompanionTheory.Hypotheses₂.isPartialZeta_zetaOfClass C, GlobalTheory.CompanionTheory.Hypotheses₂.isPartialZeta_zetaOfClassInv C', fun s h1 h2 => ?_⟩
  rw [GlobalTheory.CompanionTheory.Hypotheses₂.zetaOfClass, GlobalTheory.CompanionTheory.Hypotheses₂.zetaOfClassInv, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ψ _ => ?_
  have h := GlobalTheory.CompanionTheory.Hypotheses₂.functionalEquation_classHecke ψ D hD s h1 h2
  have e : ψ (Additive.ofMul C⁻¹) * ψ (Additive.ofMul (ClassGroup.mk0 D)) = ψ (Additive.ofMul C') := by
    rw [← AddChar.map_add_eq_mul, ← ofMul_mul, ← hC, inv_mul_cancel_left]
  calc _ = ((Fintype.card (ClassGroup (𝓞 F)) : ℂ)⁻¹ * ψ (Additive.ofMul C⁻¹)) *
        ((GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.dF F : ℂ) ^ (s / 2) * Complex.Gammaℝ s ^ Module.finrank ℚ F *
          (GlobalTheory.CompanionTheory.PartialZeta.classHecke ψ).continuedLFunction s) := by ring
    _ = _ := by
      rw [h, ← e]
      ring
