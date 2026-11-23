import Formalism.LocalToGlobal.GlobalTheory.HLatOpsP

open Module NumberField TensorProduct

noncomputable section

namespace Formalism.L2.Geo.ExtensionFiltration.ExtInvSk

open Formalism.BasicNotions Formalism.HN Formalism.HermitianLatticesTheory Formalism.L2.GlobalTheoryTheory.HLatOps

section
variable {K : Type} [Field K] [NumberField K] [StarRing K]
  (K' : Type) [Field K'] [NumberField K'] [StarRing K'] [Algebra K K']

abbrev ext (A : HLat K) (N : Submodule (𝓞 K) A.V) : Submodule (𝓞 K') (baseChange K' A).V :=
  (baseChange K' (withL A N)).L

example (A : HLat K) (N : Submodule (𝓞 K) A.V) :
    baseChange K' (withL A N) = withL (baseChange K' A) (ext K' A N) := rfl

def tau (A : HLat K) (σ : K' ≃ₐ[K] K') : (baseChange K' A).V ≃ₗ[K] (baseChange K' A).V :=
  TensorProduct.congr σ.toLinearEquiv (LinearEquiv.refl K A.V)
end

def S1 : Prop := ∀ (K K' : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  [Field K'] [NumberField K'] [StarRing K'] [IsTotallyComplex K'] [Algebra K K']
  (A : HLat K), FrameOK A → ∀ (j : ℕ) (e : Fin j → A.V), 0 < j →
  LinearIndependent K e → A.L = Submodule.span (𝓞 K) (Set.range e) → (baseChange K' A).mu = A.mu

def S2 : Prop := ∀ (K K' : Type) [Field K] [NumberField K] [StarRing K]
  [Field K'] [NumberField K'] [StarRing K'] [Algebra K K']
  (A : HLat K) (M N : Submodule (𝓞 K) A.V), N.FG → M ≤ N →
  M.toAddSubgroup.relIndex N.toAddSubgroup ≠ 0 →
  (ext K' A M).toAddSubgroup.relIndex (ext K' A N).toAddSubgroup ≠ 0 ∧
  (ext K' A M).toAddSubgroup.relIndex (ext K' A N).toAddSubgroup ≤
    M.toAddSubgroup.relIndex N.toAddSubgroup ^ finrank K K'

def S3 : Prop := ∀ (K K' : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  [Field K'] [NumberField K'] [StarRing K'] [IsTotallyComplex K'] [Algebra K K']
  (A : HLat K), FrameOK A → A.L.FG → 0 < A.rank → (baseChange K' A).mu = A.mu

def S4 : Prop := ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  (A : HLat K), FrameOK A → A.L.FG → 0 < A.rank →
  (∀ t : ℝ, A.muMax ≤ t ↔ ∀ N : Submodule (𝓞 K) A.V, N ≤ A.L → N ≠ ⊥ → (withL A N).mu ≤ t) ∧
  (∀ t : ℝ, t ≤ A.muMin ↔ ∀ N : Submodule (𝓞 K) A.V, N ≤ A.L →
    t * ((A.rank : ℝ) - (withL A N).rank) ≤ A.rank * A.mu - (withL A N).rank * (withL A N).mu)

def S5 : Prop := ∀ (K K' : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  [Field K'] [NumberField K'] [StarRing K'] [IsTotallyComplex K'] [Algebra K K']
  (A : HLat K), FrameOK A → A.L.FG → 0 < A.rank →
  A.muMax ≤ (baseChange K' A).muMax ∧ (baseChange K' A).muMin ≤ A.muMin

def S6 : Prop := ∀ (K K' K'' : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  [Field K'] [NumberField K'] [StarRing K'] [Algebra K K']
  [Field K''] [NumberField K''] [StarRing K''] [Algebra K K'']
  [Algebra K' K''] [IsScalarTower K K' K''] (A : HLat K),
  Nonempty (Iso (baseChange K'' (baseChange K' A)) (baseChange K'' A))

def ExtensionActionPermutesPlaces : Prop := ∀ (K K' : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  [Field K'] [NumberField K'] [StarRing K'] [Algebra K K']
  (A : HLat K) (σ : K' ≃ₐ[K] K') (v' : InfinitePlace K') (y : (baseChange K' A).V),
  normAt (baseChange K' A).b (baseChange K' A).X v' (tau K' A σ y) =
    normAt (baseChange K' A).b (baseChange K' A).X (v'.comap (σ : K' →+* K')) y

def GaloisDescentSubspaces : Prop := ∀ (K K' : Type) [Field K] [NumberField K] [StarRing K]
  [Field K'] [NumberField K'] [StarRing K'] [Algebra K K'] [IsGalois K K']
  (A : HLat K) (W : Submodule K' (K' ⊗[K] A.V)),
  (∀ (σ : K' ≃ₐ[K] K') (y : K' ⊗[K] A.V), y ∈ W → tau K' A σ y ∈ W) →
  ∃ W₀ : Submodule K A.V, W = W₀.baseChange K'

def ExtensionInterSubspace : Prop := ∀ (K K' : Type) [Field K] [NumberField K] [StarRing K]
  [Field K'] [NumberField K'] [StarRing K'] [Algebra K K']
  (A : HLat K), A.L.FG → ∀ (W₀ : Submodule K A.V), W₀ ≤ Submodule.span K (A.L : Set A.V) →
  ∀ (y : (baseChange K' A).V),
  y ∈ (baseChange K' A).L → (y : K' ⊗[K] A.V) ∈ W₀.baseChange K' →
  y ∈ ext K' A (A.L ⊓ W₀.restrictScalars (𝓞 K))

def ExtensionFiltrationStable : Prop := ∀ (K K' : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  [Field K'] [NumberField K'] [StarRing K'] [Algebra K K']
  (A : HLat K), FrameOK A → A.L.FG → ∀ (θ : ℝ) (σ : K' ≃ₐ[K] K') (y : (baseChange K' A).V),
  y ∈ hnStep (realize (baseChange K' A).b (baseChange K' A).X) (baseChange K' A).L θ →
  tau K' A σ y ∈ hnStep (realize (baseChange K' A).b (baseChange K' A).X) (baseChange K' A).L θ

def S7 : Prop := ∀ (K K' : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  [Field K'] [NumberField K'] [StarRing K'] [Algebra K K'] [IsGalois K K']
  (A : HLat K), FrameOK A → A.L.FG → ∀ θ : ℝ,
  ∃ N : Submodule (𝓞 K) A.V, N ≤ A.L ∧
    hnStep (realize (baseChange K' A).b (baseChange K' A).X) (baseChange K' A).L θ = ext K' A N

def S8 : Prop := ∀ (K K' : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  [Field K'] [NumberField K'] [StarRing K'] [IsTotallyComplex K'] [Algebra K K'] [IsGalois K K']
  (A : HLat K), FrameOK A → A.L.FG → 0 < A.rank →
  (baseChange K' A).muMax ≤ A.muMax ∧ A.muMin ≤ (baseChange K' A).muMin

end Formalism.L2.Geo.ExtensionFiltration.ExtInvSk
