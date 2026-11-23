import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareStanding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacFn

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open scoped GlobalTheory.VacAny

namespace GlobalTheory.HeisLatVac

theorem vacFn_apply_base_add {K κ : Type} [CommRing K] [Invertible (2 : K)] [Fintype κ] (ψ₀ : AddChar K ℂ)
    (Λ : AddSubgroup ((κ → K) × (κ → K))) (χ : (κ → K) × (κ → K) → ℂ) (x₀ : κ → K)
    (hco : ∀ u ∈ Λ, ∀ u' ∈ Λ, χ (u + u') = χ u * χ u' * ψ₀ (⅟(2 : K) * (u.1 ⬝ᵥ u'.2 - u'.1 ⬝ᵥ u.2)))
    (hY : ∀ y : κ → K, ((0 : κ → K), y) ∈ Λ → χ (0, y) = ψ₀ (x₀ ⬝ᵥ y))
    (u : (κ → K) × (κ → K)) (hu : u ∈ Λ) :
    vacFn ψ₀ Λ χ x₀ (x₀ + u.1) = χ u * ψ₀ (-(x₀ ⬝ᵥ u.2) - ⅟(2 : K) * (u.1 ⬝ᵥ u.2)) := by
  have h : ∃ u' ∈ Λ, x₀ + u.1 = x₀ + u'.1 := ⟨u, hu, rfl⟩
  rw [vacFn, dif_pos h]
  obtain ⟨hu', he⟩ := h.choose_spec
  set u' := h.choose
  have h1 : u.1 = u'.1 := add_left_cancel he
  have hd : ((0 : κ → K), u.2 - u'.2) = u - u' := by
    ext <;> simp [h1]
  have hdm : ((0 : κ → K), u.2 - u'.2) ∈ Λ := hd ▸ sub_mem hu hu'
  have hsum : u = u' + ((0 : κ → K), u.2 - u'.2) := by rw [hd]; abel
  have hχ : χ u = χ u' * ψ₀ (x₀ ⬝ᵥ (u.2 - u'.2)) * ψ₀ (⅟(2 : K) * (u'.1 ⬝ᵥ (u.2 - u'.2) - (0 : κ → K) ⬝ᵥ u'.2)) := by
    conv_lhs => rw [hsum]
    rw [hco u' hu' _ hdm, hY _ hdm]
  rw [hχ, mul_assoc, mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
  congr 2
  rw [h1]
  simp only [dotProduct_sub, zero_dotProduct]
  ring

theorem schr_vacFn : ∀ {K κ : Type} [CommRing K] [Invertible (2 : K)] [Fintype κ] (ψ₀ : AddChar K ℂ)
    (Λ : AddSubgroup ((κ → K) × (κ → K))) (χ : (κ → K) × (κ → K) → ℂ) (x₀ : κ → K),
    (∀ u ∈ Λ, ∀ u' ∈ Λ, χ (u + u') = χ u * χ u' * ψ₀ (⅟(2 : K) * (u.1 ⬝ᵥ u'.2 - u'.1 ⬝ᵥ u.2))) →
    (∀ y : κ → K, ((0 : κ → K), y) ∈ Λ → χ (0, y) = ψ₀ (x₀ ⬝ᵥ y)) →
    (∀ u ∈ Λ, ∀ w ∈ Λ, ψ₀ (u.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ u.2) = 1) →
    ∀ w ∈ Λ, GlobalTheory.WeilM.schr ψ₀ w (GlobalTheory.HeisLatVac.vacFn ψ₀ Λ χ x₀) = χ w • GlobalTheory.HeisLatVac.vacFn ψ₀ Λ χ x₀ := by
  intro K κ _ _ _ ψ₀ Λ χ x₀ hco hY hiso w hw
  funext x
  simp only [GlobalTheory.WeilM.schr, Pi.smul_apply, smul_eq_mul]
  by_cases hx : ∃ u ∈ Λ, x = x₀ + u.1
  · obtain ⟨u, hu, rfl⟩ := hx
    have e : x₀ + u.1 + w.1 = x₀ + (u + w).1 := by simp [add_assoc]
    rw [e, vacFn_apply_base_add ψ₀ Λ χ x₀ hco hY (u + w) (add_mem hu hw),
      vacFn_apply_base_add ψ₀ Λ χ x₀ hco hY u hu, hco u hu w hw]
    have h1 : ψ₀ ((x₀ + u.1) ⬝ᵥ w.2 + ⅟(2 : K) * (w.1 ⬝ᵥ w.2)) * ψ₀ (⅟(2 : K) * (u.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ u.2)) *
        ψ₀ (-(x₀ ⬝ᵥ (u + w).2) - ⅟(2 : K) * ((u + w).1 ⬝ᵥ (u + w).2)) =
        ψ₀ (-(x₀ ⬝ᵥ u.2) - ⅟(2 : K) * (u.1 ⬝ᵥ u.2)) := by
      rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
      have : (x₀ + u.1) ⬝ᵥ w.2 + ⅟(2 : K) * (w.1 ⬝ᵥ w.2) + ⅟(2 : K) * (u.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ u.2) +
          (-(x₀ ⬝ᵥ (u + w).2) - ⅟(2 : K) * ((u + w).1 ⬝ᵥ (u + w).2)) =
          (u.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ u.2) + (-(x₀ ⬝ᵥ u.2) - ⅟(2 : K) * (u.1 ⬝ᵥ u.2)) := by
        simp only [Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]
        linear_combination (-(w.1 ⬝ᵥ u.2)) * (invOf_mul_self (2 : K))
      rw [this, AddChar.map_add_eq_mul, hiso u hu w hw, one_mul]
    rw [← h1]
    ring
  · have hx' : ¬∃ u ∈ Λ, x + w.1 = x₀ + u.1 := by
      rintro ⟨u', hu', he⟩
      refine hx ⟨u' - w, sub_mem hu' hw, ?_⟩
      rw [Prod.fst_sub, ← add_sub_assoc, ← he, add_sub_cancel_right]
    simp only [vacFn, dif_neg hx, dif_neg hx', mul_zero]

end GlobalTheory.HeisLatVac
