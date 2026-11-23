import Mathlib
import Formalism.PeriodIntegrals.DivisionRowsRationalLattice

noncomputable section

namespace PI.Dv

open Formalism.BasicNotions NumberField IsDedekindDomain

def IdxCalc : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (V : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (w : HeightOneSpectrum (𝓞 K)) (M N : Submodule (𝓞 K) V),
    M.FG → N.FG → Submodule.span K (M : Set V) = Submodule.span K (N : Set V) →
    lenAt w M N ≠ ⊤ ∧
    (∀ P : Submodule (𝓞 K) V, P.FG → Submodule.span K (P : Set V) = Submodule.span K (N : Set V) →
      idxAt w M P = idxAt w M N + idxAt w N P) ∧
    (∀ (V' : Type) [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']
      (φ : V →ₗ[K] V'),
      idxAt w M N =
        idxAt w (M ⊓ (LinearMap.ker φ).restrictScalars (𝓞 K)) (N ⊓ (LinearMap.ker φ).restrictScalars (𝓞 K)) +
        idxAt w (M.map (φ.restrictScalars (𝓞 K))) (N.map (φ.restrictScalars (𝓞 K)))) ∧
    (∀ F : ℕ, LocLe w F N M → (F : ℤ) * (Formalism.HN.rkK M : ℤ) ≤ idxAt w M N) ∧
    (∀ F : ℕ, idxAt w M ((w.asIdeal ^ F) • M) = (F : ℤ) * (Formalism.HN.rkK M : ℤ)) ∧
    (∀ n : ℕ, 0 < n → N ≤ M → (∀ x ∈ M, ((n : ℕ) : 𝓞 K) • x ∈ N) →
      idxAt w M N ≤ (Formalism.HN.rkK M : ℤ) * vAdd w ((n : ℕ) : K))

end PI.Dv
