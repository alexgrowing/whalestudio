import Mathlib

set_option autoImplicit false

noncomputable section

open TensorProduct

namespace PositivityTheory.PrwZar.Qi

variable {K H : Type} [Field K] [CommRing H] [Algebra K H]

def pw (Δ : H →ₐ[K] H ⊗[K] H) (ε : H →ₐ[K] K) : ℕ → (H →ₐ[K] H)
  | 0 => (Algebra.ofId K H).comp ε
  | n + 1 => (Algebra.TensorProduct.lmul' K).comp ((Algebra.TensorProduct.map (pw Δ ε n) (AlgHom.id K H)).comp Δ)

def CounitL (Δ : H →ₐ[K] H ⊗[K] H) (ε : H →ₐ[K] K) : Prop :=
  (Algebra.TensorProduct.lmul' K).comp
    ((Algebra.TensorProduct.map ((Algebra.ofId K H).comp ε) (AlgHom.id K H)).comp Δ) = AlgHom.id K H

def CounitR (Δ : H →ₐ[K] H ⊗[K] H) (ε : H →ₐ[K] K) : Prop :=
  (Algebra.TensorProduct.lmul' K).comp
    ((Algebra.TensorProduct.map (AlgHom.id K H) ((Algebra.ofId K H).comp ε)).comp Δ) = AlgHom.id K H

def KilledCore : Prop :=
  ∀ (K H : Type) [Field K] [IsAlgClosed K] [CommRing H] [Algebra K H] [FiniteDimensional K H]
    (Δ : H →ₐ[K] H ⊗[K] H) (ε : H →ₐ[K] K), CounitL Δ ε → CounitR Δ ε →
    (∀ a b : ℕ, pw Δ ε (a * b) = (pw Δ ε a).comp (pw Δ ε b)) →
    (∃ m : ℕ, 0 < m ∧ ∀ x : H →ₐ[K] K, x.comp (pw Δ ε m) = ε) →
    ∃ N : ℕ, 0 < N ∧ pw Δ ε N = pw Δ ε 0

end PositivityTheory.PrwZar.Qi
