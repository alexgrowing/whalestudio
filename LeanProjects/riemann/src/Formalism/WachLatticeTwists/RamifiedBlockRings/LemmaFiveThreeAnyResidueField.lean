import Formalism.WachLatticeTwists.RamifiedBlockRings.ChainFromPrimitiveData
import Formalism.WachLatticeTwists.RamifiedBlockRings.RightIdealImageOfSurjective

open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.ringDataObjects

open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities Formalism.RepresentationBoundsCohomology.BR

def StatKerBc : Prop :=
  ∀ (O O' : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O'] (e : ℕ),
    (∀ y : O, IsDiscreteValuationRing.addVal O' (algebraMap O O' y) =
      e * IsDiscreteValuationRing.addVal O y) →
    ∀ (m n : Type) [Fintype m] [Fintype n] [DecidableEq n] (A : Matrix m n O),
      Module.length O' (LinearMap.ker (relMap O' (KO O') (A.map (algebraMap O O')))) =
        e * Module.length O (LinearMap.ker (relMap O (KO O) A))

def StatModuleBc : Prop :=
  ∀ (O O' : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O'] [Module.Free O O']
    [Module.Finite O O'] (e : ℕ),
    (∀ y : O, IsDiscreteValuationRing.addVal O' (algebraMap O O' y) =
      e * IsDiscreteValuationRing.addVal O y) →
    ∀ (X : Type) [Fintype X] (d G : Type) [Fintype d] [DecidableEq d] [Group G] (t : ℕ)
      (bl : d → Fin (t + 1)) (T : Subalgebra O (X → O)) (r : G →* (X → Matrix d d O)) (π : X)
      (χ₁ ε : G →* Oˣ) (g₀ : G) (eB e₁ s : X → Matrix d d O),
    DistinctEigenvalueCornerPerturbation O T r π t g₀ eB s →
    ∀ (D : RingData O X d G t bl) (D' : RingData O' X d G t bl),
      RingDef O T r π χ₁ ε g₀ eB e₁ s D →
      RingDef O' (bcT O' T) (bcR O' r) π (bcChar O' χ₁) (bcChar O' ε) g₀ (bcM O' eB) (bcM O' e₁)
        (bcM O' s) D' →
    ∀ [IsNoetherian D.R' D.R'] [∀ k, SMulCommClass D.R' O (blockRestrictedRepresentationType bl D.ρk k)]
      [∀ k, SMulCommClass D'.R' O' (blockRestrictedRepresentationType bl D'.ρk k)]
      (NN : Type) [AddCommGroup NN] [Module D.R' NN] (g : ℕ) (n : Fin g → NN),
      Submodule.span D.R' (Set.range n) = ⊤ →
      ∃ (NN' : Type) (_ : AddCommGroup NN') (_ : Module D'.R' NN') (n' : Fin g → NN'),
        Submodule.span D'.R' (Set.range n') = ⊤ ∧
        (∀ Z : Set X, (∀ x', D.p x' ∉ Z → ∃ φ : NN →ₗ[D.R'] EvalSp O d D.R' x', φ ≠ 0) →
          ∀ y', D'.p y' ∉ Z → ∃ φ : NN' →ₗ[D'.R'] EvalSp O' d D'.R' y', φ ≠ 0) ∧
        ∀ k, Module.length O' (NN' →ₗ[D'.R'] blockRestrictedRepresentationType bl D'.ρk k) =
          e * Module.length O (NN →ₗ[D.R'] blockRestrictedRepresentationType bl D.ρk k)

def StatBigResidueExt : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (N : ℕ),
    ∃ (O' : Type) (_ : CommRing O') (_ : IsDomain O') (_ : IsDiscreteValuationRing O')
      (_ : Algebra O O') (_ : Module.Free O O') (_ : Module.Finite O O'),
      (∀ y : O, IsDiscreteValuationRing.addVal O' (algebraMap O O' y) =
        IsDiscreteValuationRing.addVal O y) ∧
      (N : Cardinal) < Cardinal.mk (IsLocalRing.ResidueField O')

def LemmaFiveThreeOverExtension : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (X : Type) [Fintype X]
    (d G : Type) [Fintype d] [DecidableEq d] [Group G] (t : ℕ) (_ : 1 ≤ t) (bl : d → Fin (t + 1))
    (T : Subalgebra O (X → O)) (r : G →* (X → Matrix d d O)) (π : X) (χ₁ ε : G →* Oˣ) (g₀ : G)
    (eB e₁ s : X → Matrix d d O),
    PrimHyp O T r π bl χ₁ ε →
    AbsIrr (fun g => ((r g π).toSquareBlock bl 0).map (IsLocalRing.residue O)) →
    IdemHyp O T r π bl eB e₁ → DistinctEigenvalueCornerPerturbation O T r π t g₀ eB s →
    ∀ (D : RingData O X d G t bl), RingDef O T r π χ₁ ε g₀ eB e₁ s D →
    ∀ [IsNoetherian D.R' D.R'] [∀ k, SMulCommClass D.R' O (blockRestrictedRepresentationType bl D.ρk k)]
      (Z : Set X) (NN : Type) [AddCommGroup NN] [Module D.R' NN] (g : ℕ) (n : Fin g → NN),
      Submodule.span D.R' (Set.range n) = ⊤ →
      (∀ x', D.p x' ∉ Z → ∃ φ : NN →ₗ[D.R'] EvalSp O d D.R' x', φ ≠ 0) →
    ∀ (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O']
      [Module.Free O O'] [Module.Finite O O'] (e : ℕ),
      (∀ y : O, IsDiscreteValuationRing.addVal O' (algebraMap O O' y) =
        e * IsDiscreteValuationRing.addVal O y) →
      ((g * Fintype.card d : ℕ) : Cardinal) < Cardinal.mk (IsLocalRing.ResidueField O') →
      vcc T Z π ≤ ∑ k : Fin (t + 1), Module.length O (NN →ₗ[D.R'] blockRestrictedRepresentationType bl D.ρk k)

def LemmaFiveThreeAnyResidueField : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (X : Type) [Fintype X]
    (d G : Type) [Fintype d] [DecidableEq d] [Group G] (t : ℕ) (_ : 1 ≤ t) (bl : d → Fin (t + 1))
    (T : Subalgebra O (X → O)) (r : G →* (X → Matrix d d O)) (π : X) (χ₁ ε : G →* Oˣ) (g₀ : G)
    (eB e₁ s : X → Matrix d d O),
    PrimHyp O T r π bl χ₁ ε →
    AbsIrr (fun g => ((r g π).toSquareBlock bl 0).map (IsLocalRing.residue O)) →
    IdemHyp O T r π bl eB e₁ → DistinctEigenvalueCornerPerturbation O T r π t g₀ eB s →
    ∀ (D : RingData O X d G t bl), RingDef O T r π χ₁ ε g₀ eB e₁ s D →
    ∀ [IsNoetherian D.R' D.R'] [∀ k, SMulCommClass D.R' O (blockRestrictedRepresentationType bl D.ρk k)]
      (Z : Set X) (NN : Type) [AddCommGroup NN] [Module D.R' NN] (g : ℕ) (n : Fin g → NN),
      Submodule.span D.R' (Set.range n) = ⊤ →
      (∀ x', D.p x' ∉ Z → ∃ φ : NN →ₗ[D.R'] EvalSp O d D.R' x', φ ≠ 0) →
      vcc T Z π ≤ ∑ k : Fin (t + 1), Module.length O (NN →ₗ[D.R'] blockRestrictedRepresentationType bl D.ρk k)

end Formalism.RepresentationBoundsCohomology.ringDataObjects
