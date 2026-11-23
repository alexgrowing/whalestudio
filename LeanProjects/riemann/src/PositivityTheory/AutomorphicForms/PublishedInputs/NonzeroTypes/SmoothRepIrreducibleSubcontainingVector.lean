import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.KIface

noncomputable section

namespace UpperTheory.NonzeroTypeTheory

def SmoothRepInvariantComplement : Prop :=
  ∀ (K : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] (m : ℕ)
    (V : Representation ℂ K (Fin m → ℂ)), GlobalTheory.PRep.IsSmooth V →
    ∀ U : Submodule ℂ (Fin m → ℂ), (∀ k, ∀ u ∈ U, V k u ∈ U) →
      ∃ S : Submodule ℂ (Fin m → ℂ), IsCompl U S ∧ ∀ k, ∀ s ∈ S, V k s ∈ S

def SmoothRepIrreducibleSubcontainingVector : Prop :=
  ∀ (K : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] (m : ℕ)
    (V : Representation ℂ K (Fin m → ℂ)), GlobalTheory.PRep.IsSmooth V → ∀ v0 : Fin m → ℂ, v0 ≠ 0 →
      ∃ (S : Submodule ℂ (Fin m → ℂ)) (p : (Fin m → ℂ) →ₗ[ℂ] (Fin m → ℂ)),
        S ≠ ⊥ ∧ (∀ k, ∀ s ∈ S, V k s ∈ S) ∧
        (∀ S' : Submodule ℂ (Fin m → ℂ), S' ≤ S → (∀ k, ∀ s ∈ S', V k s ∈ S') → S' = ⊥ ∨ S' = S) ∧
        (∀ v, p v ∈ S) ∧ (∀ s ∈ S, p s = s) ∧ (∀ k v, p (V k v) = V k (p v)) ∧ p v0 ≠ 0

def SmoothRepMinimalSubrepresentation : Prop :=
  ∀ (K : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] (m : ℕ)
    (V : Representation ℂ K (Fin m → ℂ)), GlobalTheory.PRep.IsSmooth V → ∀ S : Submodule ℂ (Fin m → ℂ), S ≠ ⊥ →
      (∀ k, ∀ s ∈ S, V k s ∈ S) →
      (∀ S' : Submodule ℂ (Fin m → ℂ), S' ≤ S → (∀ k, ∀ s ∈ S', V k s ∈ S') → S' = ⊥ ∨ S' = S) →
      ∃ (d : ℕ) (ξ : Representation ℂ K (Fin d → ℂ)) (ι : (Fin d → ℂ) →ₗ[ℂ] (Fin m → ℂ)),
        Function.Injective ι ∧ LinearMap.range ι = S ∧ (∀ k v, V k (ι v) = ι (ξ k v)) ∧ ξ.IsIrreducible ∧
        GlobalTheory.PRep.IsSmooth ξ

def SchurInjectiveFromIrreducible : Prop :=
  ∀ (K : Type) [Group K] (d : ℕ) (ξ : Representation ℂ K (Fin d → ℂ)), ξ.IsIrreducible →
    ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ K W) (g : (Fin d → ℂ) →ₗ[ℂ] W), g ≠ 0 →
      (∀ k v, g (ξ k v) = ρ k (g v)) → Function.Injective g

end UpperTheory.NonzeroTypeTheory
