import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceConjugationPropertiesCmField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderEqIffConjPl
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT

theorem exists_mem_section_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (S : Set (Pl E)), IsSection S →
    ∀ u : Pl E, u ∉ S → ∃ w ∈ S, ∀ x : E, u.valuation E x = w.valuation E (IsCMField.complexConj E x) := by
  intro E _ _ _ S hS u hu
  obtain ⟨w, ⟨hwS, hwu⟩, -⟩ := hS u
  refine ⟨w, hwS, ?_⟩
  have hr : Module.finrank (maximalRealSubfield E) E = 2 := Algebra.IsQuadraticExtension.finrank_eq_two _ _
  rcases (GlobalTheory.Mem.Chr.under_eq_iff_conjPl (IsCMField.complexConj E) hr (IsCMField.complexConj_ne_one E) u w).1 hwu
    with h | h
  · exact absurd (h ▸ hwS) hu
  · intro x
    exact (h x).symm

end GlobalTheory.BCT
