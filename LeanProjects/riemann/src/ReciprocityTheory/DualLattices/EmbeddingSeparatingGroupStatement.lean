import ReciprocityTheory.DualLattices.EigenLiftsFrobeniusStatement

noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

def EmbeddingSeparatingGroupStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : ℕ) (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] [Algebra ℤ_[p] R]
    (O : Type) [CommRing O] [Algebra ℤ_[p] O] (σ : O ≃ₐ[ℤ_[p]] O) (cp : R),
    p ≠ 2 → HodgeTateSetting p v R O σ cp → ∀ (H : HodgeTateDatum p g v R O σ cp)
    (U : UnramData p g v R O σ cp H),
    ∃ (G : Type) (_ : CommGroup G) (_ : Fintype G) (β : G → O),
      (∀ γ γ', H.ρ (β (γ * γ')) = H.ρ (β γ) * H.ρ (β γ')) ∧ H.ρ (β 1) = 1 ∧
      IsUnit (Fintype.card G : R) ∧
      (∀ i γ, U.εT i ≠ 0 → U.sg (U.φ i) (β γ) = U.sg i (β γ) ^ p) ∧
      (∀ i k, U.εT i ≠ 0 → U.εT k ≠ 0 → i ≠ k →
        ∃ γ, v (algebraMap R C (U.sg i (β γ) - U.sg k (β γ))) = 1) ∧
      (∀ i, U.εT i ≠ 0 → ∃ γ, v (algebraMap R C (U.sg i (β γ) - 1)) = 1)

def EigenElementaryDivisorStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : ℕ) (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] [Algebra ℤ_[p] R]
    (O : Type) [CommRing O] [Algebra ℤ_[p] O] (σ : O ≃ₐ[ℤ_[p]] O) (cp : R),
    HodgeTateSetting p v R O σ cp → ∀ (H : HodgeTateDatum p g v R O σ cp)
    (U : UnramData p g v R O σ cp H) (X : Fin U.m → NNReal),
    (∀ i, HasLen v R (xModE H.Ht (bt2 H U) U.εT U.εL U.cj i) (X i)) →
    ∃ (κ : Ix g → Fin U.m) (Λ : Matrix (Ix g) (Ix g) R) (ε : Ix g → R),
      IsUnit Λ.det ∧ (∀ j, Matrix.vecMul (Λ j) (U.εT (κ j)) = Λ j) ∧
      (∀ j, ∃ c, cp = ε j * c) ∧
      (∀ i, ∏ j ∈ Finset.univ.filter (fun j => κ j = i), v (algebraMap R C (ε j)) = X i) ∧
      (∀ i (n : ℕ), Nonempty (LinearMap.range (Matrix.mulVecLin (U.εT i)) ≃ₗ[R] (Fin n → R)) →
        (Finset.univ.filter fun j => κ j = i).card = n) ∧
      (∀ i, Submodule.span R (Set.range fun k => (fromRows H.Ht (bt2 H U) * U.εT i) k) =
        Submodule.span R ((fun j => ε j • Λ j) '' {j | κ j = i}))

def EigenRankStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : ℕ) (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] [Algebra ℤ_[p] R]
    (O : Type) [CommRing O] [Algebra ℤ_[p] O] (σ : O ≃ₐ[ℤ_[p]] O) (cp : R),
    HodgeTateSetting p v R O σ cp → ∀ (H : HodgeTateDatum p g v R O σ cp) (U : UnramData p g v R O σ cp H),
    (∀ i, ∃ n : ℕ, Nonempty (LinearMap.range (Matrix.mulVecLin (U.εT i)) ≃ₗ[R] (Fin n → R)) ∧
      Nonempty (LinearMap.range (Matrix.mulVecLin (U.εT (U.φ i))) ≃ₗ[R] (Fin n → R))) ∧
    (∀ i, U.εT i = 0 → U.r i = 0)

end ReciprocityTheory.PGsh.Up
