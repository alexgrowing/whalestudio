import Formalism.LocalRingCardinality.PrincipalHermitianLattice

noncomputable section

namespace Formalism.BasicNotions

open NumberField

def DV.Used (D : D7) (μ : D.what₂.Tup) : Prop :=
  μ = D.what₂.mu0 ∨ μ = D.what₂.muStar ∨ μ = D.what₂.muStar' ∨ ∃ w, μ = D.what₂.muAt w

structure AmbForm (D : D7) {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE]
    [FiniteDimensional ℂ EE] (S : RowSide D EE) where

  MtH : D.what₂.Tup → HLat D.what₂.LL

  jAmb : ∀ μ, (MtH μ).V →ₛₗ[D.what₂.embLL] S.Amb μ
  MtH_good : ∀ μ, DV.Used D μ → (MtH μ).Good
  jAmb_basis : ∀ μ, DV.Used D μ → LinearIndependent ℂ (fun i => jAmb μ ((MtH μ).b i)) ∧
    Submodule.span ℂ (Set.range (fun i => jAmb μ ((MtH μ).b i))) = ⊤

  jAmb_lat : ∀ μ, DV.Used D μ → ∀ x, x ∈ (MtH μ).L ↔ ∃ c : S.Amb μ → 𝓞 D.what₂.LL,
    jAmb μ x = ∑ v ∈ (S.Mtilde μ).gen, D.what₂.embLL ((c v : 𝓞 D.what₂.LL) : D.what₂.LL) • v

  jAmb_gen : ∀ μ, DV.Used D μ → ∀ v ∈ (S.Mtilde μ).gen, v ∈ Set.range (jAmb μ)

  jAmb_norm : ∀ μ, DV.Used D μ → ∀ x,
    Formalism.HermitianLatticesTheory.normAt (MtH μ).b (MtH μ).X (InfinitePlace.mk D.what₂.embLL) x = ‖jAmb μ x‖

end Formalism.BasicNotions

end
