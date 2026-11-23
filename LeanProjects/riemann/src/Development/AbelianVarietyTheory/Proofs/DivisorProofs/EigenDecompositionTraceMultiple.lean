import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SandwichMaps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomsLinearlyIndependentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceEqSumEigenMultiplicitiesStatement
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps

namespace GlobalTheory

theorem finrank_eig_eq_mul_of_trace_eq_mul :
    ∀ (C : Type) [Field C] [CharZero C] (O : Type) [CommRing O] [Algebra O C] (Λ : Type) [CommRing Λ]
      (h h' m : ℕ) (ρ : Λ → Matrix (Fin h) (Fin h) O) (ρ' : Λ → Matrix (Fin h') (Fin h') O),
      Function.Injective (algebraMap O C) → iSupIndep (fun σ : Λ →+* O => eig C ρ σ) →
      (⨆ σ : Λ →+* O, eig C ρ σ) = ⊤ → iSupIndep (fun σ : Λ →+* O => eig C ρ' σ) →
      (⨆ σ : Λ →+* O, eig C ρ' σ) = ⊤ → (∀ a, (ρ a).trace = (m : O) * (ρ' a).trace) →
      ∀ τ : Λ →+* O, Module.finrank C (eig C ρ τ) = m * Module.finrank C (eig C ρ' τ) := by
  intro C _ _ O _ _ Λ _ h h' m ρ ρ' hinj hind htop hind' htop' htr τ
  obtain ⟨hf, hsum⟩ := GlobalTheory.T.trace_eq_sum_eigen_multiplicities C O Λ h ρ hind htop
  obtain ⟨hf', hsum'⟩ := GlobalTheory.T.trace_eq_sum_eigen_multiplicities C O Λ h' ρ' hind' htop'
  classical
  let S : Finset (Λ →+* O) := insert τ (hf.toFinset ∪ hf'.toFinset)
  have hS : ∀ σ, eig C ρ σ ≠ ⊥ → σ ∈ S := fun σ hσ =>
    Finset.mem_insert_of_mem (Finset.mem_union_left _ (hf.mem_toFinset.2 hσ))
  have hS' : ∀ σ, eig C ρ' σ ≠ ⊥ → σ ∈ S := fun σ hσ =>
    Finset.mem_insert_of_mem (Finset.mem_union_right _ (hf'.mem_toFinset.2 hσ))
  let c : (Λ →+* O) → C := fun σ =>
    (Module.finrank C (eig C ρ σ) : C) - (m : C) * (Module.finrank C (eig C ρ' σ) : C)
  have key : ∀ a : Λ, ∑ σ ∈ S, c σ * algebraMap O C (σ a) = 0 := by
    intro a
    have e1 := hsum S hS a
    have e2 := hsum' S hS' a
    simp only [c, sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
    rw [← e1, ← e2, htr a, map_mul, map_natCast, sub_self]
  have hc := GlobalTheory.T.ring_homs_linearly_independent C O Λ hinj S c key τ (Finset.mem_insert_self _ _)
  have : (Module.finrank C (eig C ρ τ) : C) = (m : C) * (Module.finrank C (eig C ρ' τ) : C) :=
    sub_eq_zero.1 hc
  exact_mod_cast this

end GlobalTheory
