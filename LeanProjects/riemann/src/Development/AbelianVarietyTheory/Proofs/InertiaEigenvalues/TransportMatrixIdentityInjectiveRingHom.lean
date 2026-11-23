import Mathlib
open Matrix

namespace GlobalTheory

theorem transport_matrix_identity_star_alg :
    ∀ {R L : Type} [CommRing R] [CommRing L] (ι : R →+* L), Function.Injective ι →
    ∀ (d N q : ℕ) (p : Fin d → ℕ) (ξ s : R) (Qm Q₁ : Matrix (Fin d) (Fin d) L)
      (X B c V : Matrix (Fin d) (Fin d) R),
      ι s ^ N • Qm = (X * B).map ι → (∀ i j, ι ξ ^ q * Q₁ i j = ι (ξ ^ p j * V i j)) →
      Q₁ = Qm * c.map ι →
      ξ ^ q • (X * B * c) = s ^ N • (V * Matrix.diagonal (fun j => ξ ^ p j)) := by
  intro R L _ _ ι hι d N q p ξ s Qm Q₁ X B c V h1 h2 h3
  have key : (X * B * c).map ι = ι s ^ N • Q₁ := by
    rw [Matrix.map_mul, ← h1, h3, Matrix.smul_mul]
  ext i j
  apply hι
  have e : ι ((X * B * c) i j) = ι s ^ N * Q₁ i j := by
    have := congrFun (congrFun key i) j
    simpa [Matrix.map_apply, Matrix.smul_apply] using this
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.mul_diagonal, map_mul, map_pow]
  rw [e]
  have h := h2 i j
  simp only [map_mul, map_pow] at h
  calc ι ξ ^ q * (ι s ^ N * Q₁ i j) = ι s ^ N * (ι ξ ^ q * Q₁ i j) := by ring
    _ = ι s ^ N * (ι ξ ^ p j * ι (V i j)) := by rw [h]
    _ = ι s ^ N * (ι (V i j) * ι ξ ^ p j) := by ring

end GlobalTheory
