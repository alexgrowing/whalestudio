import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspidalPairIrreducibleProductStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicProductEquivProductOfPartitionStatement
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

noncomputable section

namespace GlobalTheory

theorem isSubquotient_prod₂_of_cuspSupport_reorder : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.UnlinkedProductIrreducible → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t s : ℕ) (π : Irr k (r + t)) (d : Fin s → ℕ) (σ : ∀ a, Irr k (d a)) (S : Finset (Fin s)), IsCuspSupport π.π d (fun a => (σ a).π) → (∀ b ∈ S, d b = 1) → (∀ a b, a ∉ S → b ∈ S → ∀ (h : d a = d b) (α : ℂˣ), ¬ Nonempty ((h ▸ σ a : Irr k (d b)).π.Equiv (twist (σ b).π (detChar (Fin (d b)) (unrChar k α))))) → ∑ a ∈ Sᶜ, d a = r → ∑ a ∈ S, d a = t → ∃ (s₁ s₂ : ℕ) (ι₁ : Fin s₁ → Fin s) (ι₂ : Fin s₂ → Fin s) (e₁ : (Σ a, Fin (d (ι₁ a))) ≃ Fin r) (e₂ : (Σ b, Fin (d (ι₂ b))) ≃ Fin t) (V₁ V₂ : Type) (_ : AddCommGroup V₁) (_ : Module ℂ V₁) (_ : AddCommGroup V₂) (_ : Module ℂ V₂) (ρ₁ : Representation ℂ (GL (Fin r) k) V₁) (ρ₂ : Representation ℂ (GL (Fin t) k) V₂), (∀ a, ι₁ a ∉ S) ∧ (∀ b, ι₂ b ∈ S) ∧ IsSmooth ρ₁ ∧ IsSmooth ρ₂ ∧ Nonempty (ρ₁.Equiv (multiProd e₁ fun a => (σ (ι₁ a)).π)) ∧ Nonempty (ρ₂.Equiv (multiProd e₂ fun b => (σ (ι₂ b)).π)) ∧ IsSubquotient π.π (prod₂ ρ₁ ρ₂) := by
  intro hBZ hGL hUPI k _ _ _ _ r t s π d σ S hsupp hS hunl hr ht
  obtain ⟨-, hσ, e, hsub⟩ := hsupp
  have sumc : ∀ (T : Finset (Fin s)), ∑ a : Fin T.card, d (T.orderEmbOfFin rfl a) = ∑ a ∈ T, d a := by
    intro T
    rw [← Finset.sum_coe_sort T]
    exact Fintype.sum_equiv (T.orderIsoOfFin rfl).toEquiv _ _ (fun a => by simp)
  have c₁ : Fintype.card (Σ a : Fin Sᶜ.card, Fin (d (Sᶜ.orderEmbOfFin rfl a))) = Fintype.card (Fin r) := by
    simp [Fintype.card_sigma, sumc, hr]
  have c₂ : Fintype.card (Σ b : Fin S.card, Fin (d (S.orderEmbOfFin rfl b))) = Fintype.card (Fin t) := by
    simp [Fintype.card_sigma, sumc, ht]
  let e₁ := Fintype.equivOfCardEq c₁
  let e₂ := Fintype.equivOfCardEq c₂
  obtain ⟨φ⟩ := GlobalTheory.T.parabolicProduct_equiv_product_of_partition k s d σ S r t e e₁ e₂ (fun a b ha hb n _ _ f f' =>
    GlobalTheory.T.cuspidal_pair_irreducible_product hBZ hGL hUPI k n (fun i => d (![a, b] i)) (fun i => σ (![a, b] i))
      (fun i => ⟨(hσ _).1, (hσ _).2.2⟩) (hS b hb) (hunl a b ha hb) f f')
  refine ⟨Sᶜ.card, S.card, fun a => Sᶜ.orderEmbOfFin rfl a, fun b => S.orderEmbOfFin rfl b, e₁, e₂, _, _,
    inferInstance, inferInstance, inferInstance, inferInstance,
    multiProd e₁ fun a => (σ (Sᶜ.orderEmbOfFin rfl a)).π, multiProd e₂ fun b => (σ (S.orderEmbOfFin rfl b)).π,
    fun a => Finset.mem_compl.1 (Finset.orderEmbOfFin_mem Sᶜ rfl a),
    fun b => Finset.orderEmbOfFin_mem S rfl b, isSmooth_parInd _ _, isSmooth_parInd _ _,
    ⟨Representation.Equiv.refl _⟩, ⟨Representation.Equiv.refl _⟩, ?_⟩
  exact hsub.trans (IsSubquotient.of_surjective φ.symm.toIntertwiningMap φ.symm.toLinearEquiv.surjective)

end GlobalTheory

end
