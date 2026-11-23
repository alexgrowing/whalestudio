import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSubquotientProdReorderedCuspSupport
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.UnlinkedProductIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.DepthZeroJacquetInjective
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsInSupportOfMultiProd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InSupportOfIsSubquotient
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NotInSupportOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivDetCharacterOfIrreducibleRankLeOne
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSubquotient_prod_reordered_cuspSupport : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.UnlinkedProductIrreducible → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t s : ℕ) (π : Irr k (r + t)) (d : Fin s → ℕ) (σ : ∀ a, Irr k (d a)) (S : Finset (Fin s)), IsCuspSupport π.π d (fun a => (σ a).π) → (∀ b ∈ S, d b = 1) → (∀ a b, a ∉ S → b ∈ S → ∀ (h : d a = d b) (α : ℂˣ), ¬ Nonempty ((h ▸ σ a : Irr k (d b)).π.Equiv (twist (σ b).π (detChar (Fin (d b)) (unrChar k α))))) → ∑ a ∈ Sᶜ, d a = r → ∑ a ∈ S, d a = t → ∃ (s₁ s₂ : ℕ) (ι₁ : Fin s₁ → Fin s) (ι₂ : Fin s₂ → Fin s) (e₁ : (Σ a, Fin (d (ι₁ a))) ≃ Fin r) (e₂ : (Σ b, Fin (d (ι₂ b))) ≃ Fin t) (V₁ V₂ : Type) (_ : AddCommGroup V₁) (_ : Module ℂ V₁) (_ : AddCommGroup V₂) (_ : Module ℂ V₂) (ρ₁ : Representation ℂ (GL (Fin r) k) V₁) (ρ₂ : Representation ℂ (GL (Fin t) k) V₂), (∀ a, ι₁ a ∉ S) ∧ (∀ b, ι₂ b ∈ S) ∧ IsSmooth ρ₁ ∧ IsSmooth ρ₂ ∧ Nonempty (ρ₁.Equiv (multiProd e₁ fun a => (σ (ι₁ a)).π)) ∧ Nonempty (ρ₂.Equiv (multiProd e₂ fun b => (σ (ι₂ b)).π)) ∧ IsSubquotient π.π (prod₂ ρ₁ ρ₂) := by
  first | exact @GlobalTheory.isSubquotient_prod₂_of_cuspSupport_reorder | exact GlobalTheory.isSubquotient_prod₂_of_cuspSupport_reorder | (intros; apply GlobalTheory.isSubquotient_prod₂_of_cuspSupport_reorder <;> assumption)
