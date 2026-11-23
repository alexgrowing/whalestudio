import Mathlib

noncomputable section

namespace PI.VolStabW

def ffH {K : Type} [CommRing K] (σ : K →+* K) {M : ℕ} (J : Matrix (Fin M) (Fin M) K)
    (x y : Fin M → K) : K :=
  ∑ i, ∑ j, σ (x i) * J i j * y j

def ffGram {K : Type} [CommRing K] (σ : K →+* K) {M a : ℕ} (J : Matrix (Fin M) (Fin M) K)
    (X : Fin a → Fin M → K) : Matrix (Fin a) (Fin a) K :=
  fun i j => ffH σ J (X i) (X j)

def IsQuadInv (k K : Type) [Field k] [CommRing K] [Algebra k K] (σ : K ≃ₐ[k] K) : Prop :=
  (∀ x, σ (σ x) = x) ∧
    ((IsField K ∧ Module.finrank k K = 2 ∧ σ ≠ AlgEquiv.refl) ∨
      ∃ e : K ≃ₐ[k] k × k, ∀ x, e (σ x) = (e x).swap)

def FFCount : Prop :=
  ∀ M : ℕ, ∃ C : ℝ, ∀ (k K : Type) [Field k] [Finite k] [CommRing K] [Algebra k K]
    (σ : K ≃ₐ[k] K), IsQuadInv k K σ → (2 : k) ≠ 0 →
    ∀ J : Matrix (Fin M) (Fin M) K, (∀ i j, σ (J j i) = J i j) → IsUnit J.det →
    ∀ a : ℕ, a + 2 ≤ M → ∀ T : Matrix (Fin a) (Fin a) K, (∀ i j, σ (T j i) = T i j) →
    IsUnit T.det →
    |(Nat.card {X : Fin a → Fin M → K // ffGram (σ : K →+* K) J X = T} : ℝ) /
        (Nat.card k : ℝ) ^ (2 * M * a - a ^ 2) - 1| ≤ C * ((Nat.card k : ℝ)⁻¹) ^ 2

def FFSplit : Prop :=
  ∀ (k : Type) [Field k] [Finite k] (M a : ℕ), a ≤ M →
    ∀ J : Matrix (Fin M) (Fin M) (k × k), (∀ i j, (J j i).swap = J i j) → IsUnit J.det →
    ∀ T : Matrix (Fin a) (Fin a) (k × k), (∀ i j, (T j i).swap = T i j) → IsUnit T.det →
    (Nat.card {X : Fin a → Fin M → k × k //
        ffGram (RingEquiv.prodComm (R := k) (S := k)).toRingHom J X = T} : ℝ) =
      (∏ i : Fin a, ((Nat.card k : ℝ) ^ M - (Nat.card k : ℝ) ^ (i : ℕ))) *
        (Nat.card k : ℝ) ^ (a * (M - a))

def FFInert : Prop :=
  ∀ (k K : Type) [Field k] [Finite k] [Field K] [Algebra k K] (σ : K ≃ₐ[k] K),
    (∀ x, σ (σ x) = x) → Module.finrank k K = 2 → σ ≠ AlgEquiv.refl → (2 : k) ≠ 0 →
    ∀ (M a : ℕ), a ≤ M →
    ∀ J : Matrix (Fin M) (Fin M) K, (∀ i j, σ (J j i) = J i j) → IsUnit J.det →
    ∀ T : Matrix (Fin a) (Fin a) K, (∀ i j, σ (T j i) = T i j) → IsUnit T.det →
    (Nat.card {X : Fin a → Fin M → K // ffGram (σ : K →+* K) J X = T} : ℝ) =
      ∏ j : Fin a, ((Nat.card k : ℝ) ^ (2 * (M - j) - 1) -
        (-1) ^ (M - j) * (Nat.card k : ℝ) ^ (M - j - 1))

end PI.VolStabW
