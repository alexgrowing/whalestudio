import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TypeLocalGlobal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TypeParameterSquarefree
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.CompatR
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.GoodRCongr
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.SplitBCOfGalIso
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.CardRootsBar

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
open Polynomial
open GlobalTheory.TypeAbove

noncomputable section

namespace UpperTheory.GalS

open UpperTheory.Lit.Car (IneAb comm_le_ine)

theorem comm_triv {G : Type} [Group G] (I : Subgroup G) (φ : G → ℂ) (h1 : φ 1 = 1)
    (hm : ∀ a ∈ I, ∀ b ∈ I, φ (a * b) = φ a * φ b) : ∀ σ ∈ ⁅I, I⁆, φ σ = 1 := by
  have hinv : ∀ a ∈ I, φ a * φ a⁻¹ = 1 := fun a ha => by
    rw [← hm a ha a⁻¹ (I.inv_mem ha), mul_inv_cancel, h1]
  let K : Subgroup G :=
    { carrier := {x | x ∈ I ∧ φ x = 1}
      mul_mem' := fun {x y} hx hy => ⟨I.mul_mem hx.1 hy.1, by rw [hm x hx.1 y hy.1, hx.2, hy.2, one_mul]⟩
      one_mem' := ⟨I.one_mem, h1⟩
      inv_mem' := fun {x} hx => ⟨I.inv_mem hx.1, by simpa [hx.2] using hinv x hx.1⟩ }
  have hle : ⁅I, I⁆ ≤ K := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    refine ⟨I.mul_mem (I.mul_mem (I.mul_mem ha hb) (I.inv_mem ha)) (I.inv_mem hb), ?_⟩
    rw [commutatorElement_def, hm _ (I.mul_mem (I.mul_mem ha hb) (I.inv_mem ha)) _ (I.inv_mem hb),
      hm _ (I.mul_mem ha hb) _ (I.inv_mem ha), hm a ha b hb]
    linear_combination φ b * φ b⁻¹ * hinv a ha + hinv b hb
  exact fun σ hσ => (hle hσ).2

end UpperTheory.GalS

end
