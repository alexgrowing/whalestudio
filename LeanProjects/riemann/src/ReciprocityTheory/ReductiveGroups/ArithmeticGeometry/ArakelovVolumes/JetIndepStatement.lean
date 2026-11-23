import Mathlib

namespace ReciprocityTheory.ChartRestriction.G.AR

def multiLt (D a : ℕ) : Finset (Fin D → ℕ) :=
  (Finset.range a).biUnion (fun d => Finset.Nat.antidiagonalTuple D d)

def JetIndepStatement.{u, v, w} : Prop :=
  ∀ (K : Type u) (A : Type v) (H : Type w) [Field K] [CommRing A] [Algebra K A]
    [AddCommGroup H] [Module A H] [Module K H] [IsScalarTower K A H]
    (J : Ideal A) (D a0 T δ : ℕ) (s : Fin D → A) (w0 : A) (t : Fin δ → H),
    (∀ k, s k ∈ J) →
    (∀ a < a0, ∀ h : (Fin D → ℕ) → H,
      (∑ α ∈ Finset.Nat.antidiagonalTuple D a, (∏ k, s k ^ α k) • h α) ∈ (J ^ (a + 1)) • (⊤ : Submodule A H) →
      ∀ α ∈ Finset.Nat.antidiagonalTuple D a, h α ∈ J • (⊤ : Submodule A H)) →
    (∃ u : A, u * w0 - 1 ∈ J) →
    (∀ c : Fin δ → K, (∑ i, c i • t i) ∈ J • (⊤ : Submodule A H) → c = 0) →
    ∀ c : (Fin D → ℕ) → Fin δ → K,
      (∑ α ∈ multiLt D a0, ∑ i, c α i • (((∏ k, s k ^ α k) * w0 ^ (T - ∑ k, α k)) • t i)) ∈
          (J ^ a0) • (⊤ : Submodule A H) →
      ∀ α ∈ multiLt D a0, ∀ i, c α i = 0

end ReciprocityTheory.ChartRestriction.G.AR
