import Formalism.WachLatticeTwists.ShapeRowIsomorphisms.StatBKInIso
import Formalism.WachLatticeTwists.CoprimeLiftBounds.StatBridgeChiOne

open Formalism.NG
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC Formalism.RepresentationBoundsCohomology.JT Formalism.RepresentationBoundsCohomology.BR

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology

def clsRow {O Γ VT VT' : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
    [Group Γ] [TopologicalSpace Γ]
    [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT] [ContinuousSMul O VT]
    [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT'] [ContinuousSMul O VT']
    (D : LatData O Γ VT VT') {T₂ : Type} [AddCommGroup T₂] [Module O T₂] (v : T₂ ≃ₗ[O] D.T')
    (f : Γ → T₂) : ReciprocityTheory.Gal.H1 D.ρTl' := by
  classical
  exact if h : (fun g => v (f g)) ∈ ReciprocityTheory.Gal.Z1 D.ρTl' then Submodule.Quotient.mk ⟨_, h⟩ else 0

def StatClause5Row : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
    (VT VT' : Type)
    [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT] [ContinuousSMul O VT]
    [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT'] [ContinuousSMul O VT']
    (A T' G : Type) [Ring A] [Algebra O A] [CommRing T'] [Algebra T' A] [Group G]
    (M : Type) [AddCommGroup M] [Module A M] [Module O M] [SMulCommClass A O M]
    (r : G →* A) (χ : G →* T'ˣ) (Dw : Subgroup G) [TopologicalSpace Dw] (ε : G →* Oˣ)
    (T₁ T₂ : Type) [AddCommGroup T₁] [Module O T₁] [AddCommGroup T₂] [Module O T₂]
    (ρ₁ : Representation O G T₁) (ρ₂ : Representation O G T₂) (π : T₁ →ₗ[O] T₂)
    (γ : T₂ →ₗ[O] M →ₗ[O] KO O)
    (D : LatData O Dw VT VT') (u : M ≃ₗ[O] (VT ⧸ D.T))
    (hu : ∀ g m, u (resRep (uRep O (M := M) r χ) Dw g m) = D.ρA g (u m)) (v : T₂ ≃ₗ[O] D.T'),
    (∀ g : Dw, D.ε g = ε g) → ContAction D.ρT → IsEquivMap ρ₁ ρ₂ π →
    (∀ (g : Dw) t, v (ρ₂ g t) = D.ρTl' g (v t)) → (∀ t m, γ t m = pairKO D.bT D.T (u m) (v t)) →
    ∀ hk : Function.Injective (kRow D _ u hu),
    ∀ C₁ : (Dw → T₁) → Prop, (∀ a, C₁ a → Continuous fun g => v (π (a g))) →
    ∀ (a : Dw → T₁) (b : coZ1s (resRep (uRep O (M := M) r χ) Dw))
      (hb : Submodule.mkQ _ b ∈ LinearMap.range (kRow D _ u hu)), a ∈ characterColumnKernelSet (resRep ρ₁ Dw) → C₁ a →
      (∃ c : Dw → KO O, Continuous c ∧ ∀ g h : Dw, γ (π (a g)) (uElt r χ (g : G) • (b : Dw → M) h) =
        ((ε (g : G) : Oˣ) : O) • c h - c (g * h) + c g) →
      prK D _ hk ⟨Submodule.mkQ _ b, hb⟩ (clsRow D v (fun g => π (a g))) = 0

end Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology
