import Formalism.WachLatticeTwists.CharacterSplitJumps.WachTwistTheoremFromTorsionBound
import Formalism.WachLatticeTwists.CupProductVanishing.Statement

open Formalism.NG
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC Formalism.RepresentationBoundsCohomology.JT Formalism.RepresentationBoundsCohomology.T2
open ReciprocityTheory.ChartRestriction.T2 (GK PadicCoeff FracTop IsCyc RealLatG fracBilinear)

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology

section Defs

variable {O Γ VT VT' : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
    [Group Γ] [TopologicalSpace Γ]
    [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT]
    [ContinuousSMul O VT]
    [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT']
    [ContinuousSMul O VT'] {X : Type} [AddCommGroup X] [Module O X]

def qK (D : LatData O Γ VT VT') (k : H1 D.ρA →ₗ[O] X) (hk : Function.Injective k) :
    H1 D.ρT →ₗ[O] LinearMap.range k :=
  (LinearEquiv.ofInjective k hk).toLinearMap ∘ₗ D.q

def prK (D : LatData O Γ VT VT') (k : H1 D.ρA →ₗ[O] X) (hk : Function.Injective k) :
    LinearMap.range k →ₗ[O] H1 D.ρTl' →ₗ[O] KO O :=
  D.pr ∘ₗ (LinearEquiv.ofInjective k hk).symm.toLinearMap

def kRow (D : LatData O Γ VT VT') {M : Type} [AddCommGroup M] [Module O M] (ρM : Representation O Γ M)
    (u : M ≃ₗ[O] (VT ⧸ D.T)) (hu : ∀ g m, u (ρM g m) = D.ρA g (u m)) : H1 D.ρA →ₗ[O] H1z ρM :=
  ReciprocityTheory.ChartRestriction.T2.traceH1 (MulEquiv.refl Γ) u ρM D.ρA hu ∘ₗ ReciprocityTheory.ChartRestriction.T2.toH1Cocycles D.ρA

end Defs

def StatBKInIso : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
    (VT VT' : Type)
    [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT]
    [ContinuousSMul O VT] [Module (FractionRing O) VT] [IsScalarTower O (FractionRing O) VT]
    [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT']
    [ContinuousSMul O VT'] [Module (FractionRing O) VT'] [IsScalarTower O (FractionRing O) VT']
    (G : Type) [Group G] [TopologicalSpace G] (D : LatData O G VT VT') (i : G ≃ₜ* GK p K)
    (X : Type) [AddCommGroup X] [Module O X] (k : H1 D.ρA →ₗ[O] X) (hk : Function.Injective k)
    [Module (FractionRing O) (H1 D.ρT)] [IsScalarTower O (FractionRing O) (H1 D.ρT)]
    [Module (FractionRing O) (H1 D.ρT')] [IsScalarTower O (FractionRing O) (H1 D.ρT')]
    (HfV : Submodule (FractionRing O) (H1 D.ρT)) (HfV' : Submodule (FractionRing O) (H1 D.ρT')),
    FiniteDimensional ℚ_[p] K → PadicCoeff p O → FracTop O → RealLatG i D →
    Function.Injective D.inv → Function.Injective D.invF → D.InvCompat →
    (∀ a, a ∈ HfV ↔ ∀ b ∈ HfV', fracBilinear (pairF D) a b = 0) →
    BKIn (LinearMap.range k) (qK D k hk) D.j' (prK D k hk) (fracBilinear (pairF D)) HfV HfV'
      (((HfV.restrictScalars O).map D.q).map k) ((HfV'.restrictScalars O).comap D.j')

def StatKRowInj : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
    (VT VT' : Type)
    [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT] [ContinuousSMul O VT]
    [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT'] [ContinuousSMul O VT']
    (G : Type) [Group G] [TopologicalSpace G] (D : LatData O G VT VT')
    (M : Type) [AddCommGroup M] [Module O M] (ρM : Representation O G M)
    (u : M ≃ₗ[O] (VT ⧸ D.T)) (hu : ∀ g m, u (ρM g m) = D.ρA g (u m)), Function.Injective (kRow D ρM u hu)

def StatBKInRow : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
    (VT VT' : Type)
    [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT]
    [ContinuousSMul O VT] [Module (FractionRing O) VT] [IsScalarTower O (FractionRing O) VT]
    [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT']
    [ContinuousSMul O VT'] [Module (FractionRing O) VT'] [IsScalarTower O (FractionRing O) VT']
    (A T' G : Type) [Ring A] [Algebra O A] [CommRing T'] [Algebra T' A] [Group G]
    (M : Type) [AddCommGroup M] [Module A M] [Module O M] [SMulCommClass A O M]
    (r : G →* A) (χ : G →* T'ˣ) (Dw : Subgroup G) [TopologicalSpace Dw]
    (D : LatData O Dw VT VT') (i : Dw ≃ₜ* GK p K) (u : M ≃ₗ[O] (VT ⧸ D.T))
    (hu : ∀ g m, u (resRep (uRep O (M := M) r χ) Dw g m) = D.ρA g (u m))
    [Module (FractionRing O) (H1 D.ρT)] [IsScalarTower O (FractionRing O) (H1 D.ρT)]
    [Module (FractionRing O) (H1 D.ρT')] [IsScalarTower O (FractionRing O) (H1 D.ρT')]
    (HfV : Submodule (FractionRing O) (H1 D.ρT)) (HfV' : Submodule (FractionRing O) (H1 D.ρT')),
    FiniteDimensional ℚ_[p] K → PadicCoeff p O → FracTop O → RealLatG i D →
    Function.Injective D.inv → Function.Injective D.invF → D.InvCompat →
    (∀ a, a ∈ HfV ↔ ∀ b ∈ HfV', fracBilinear (pairF D) a b = 0) →
    ∃ hk : Function.Injective (kRow D _ u hu),
    BKIn (LinearMap.range (kRow D _ u hu)) (qK D _ hk) D.j' (prK D _ hk) (fracBilinear (pairF D)) HfV HfV'
      (((HfV.restrictScalars O).map D.q).map (kRow D _ u hu)) ((HfV'.restrictScalars O).comap D.j')

end Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology
