import Formalism.CyclotomicNorms.StatementTW

open Finset Polynomial

noncomputable section

namespace Formalism.CyclotomicNorms

def TWAbsUniform : Prop :=
  ∀ (K L : Type) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K] [CharZero K]
    [NormedField L] [IsUltrametricDist L] [NormedAlgebra K L] [IsAlgClosed L]
    [Algebra.IsAlgebraic K L]
    (ℓ e e₀ R' D' m₁ t M₀ : ℕ) (O₀ O : Subring K) [IsDiscreteValuationRing O₀]
    [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O₀)] (w₀ : O₀) (w : O)
    (Sig JJ : Type) [Fintype Sig] [Fintype JJ] (vv : JJ → ℝ)
    (F : ℕ → Sig → MvPolynomial (Fin R' ⊕ Fin R') O₀)
    (f : ℕ → JJ → MvPolynomial (Fin R' ⊕ Fin R') O) (D g : ℕ → JJ → MvPolynomial (Fin R') O),
    ℓ.Prime → 0 < e → 0 < e₀ → ‖(ℓ : K)‖ = (ℓ : ℝ)⁻¹ →
    (∀ x : K, x ≠ 0 → ∃ n : ℤ, vl ℓ x = n / e) →
    (∀ x : O₀, ‖(x : K)‖ ≤ 1) → (∀ x : O, ‖(x : K)‖ ≤ 1) →
    Irreducible w₀ → Irreducible w → vl ℓ (w₀ : K) = 1 / e₀ → vl ℓ (w : K) = 1 / e →
    (∀ j, ∃ n : ℕ, vv j = n / e) →

    (∀ M, M₀ ≤ M → ∀ s, F M s ∉
      Ideal.span {MvPolynomial.C ((ℓ : O₀) ^ (if ℓ = 2 then 1 else 0) * w₀)} +
        varIdeal O₀ (Fin R' ⊕ Fin R') ^ (D' + 1) + lamIdeal O₀ (Fin R' ⊕ Fin R') ℓ M) →

    (∀ M, M₀ ≤ M → ∀ j,
      MvPolynomial.bind₁ (Sum.elim MvPolynomial.X (fun _ => 0)) (f M j) - D M j * g M j ∈
        lamIdeal O (Fin R') ℓ M ∧
      ((MvPolynomial.constantCoeff (g M j) : O) : K) ≠ 0 ∧
      vl ℓ ((MvPolynomial.constantCoeff (g M j) : O) : K) = vv j ∧
      FewFactors ℓ M m₁ (D M j)) →
    ∀ ε : ℝ, 0 < ε →
      ∃ (M k : ℕ) (e'' e' : Fin R' → ℕ) (z : L), M₀ ≤ M ∧ k ≤ M ∧ (∀ i, e'' i < k ∧ e' i < k) ∧
        IsPrimitiveRoot z (ℓ ^ k) ∧ ∀ sg : Sig ⊕ JJ → ℤˣ,
        (∀ s, MvPolynomial.eval₂ ((algebraMap K L).comp O₀.subtype)
            (evTw ℓ z e'' e' (sg (Sum.inl s))) (F M s) ≠ 0) ∧
        (∀ j, MvPolynomial.eval₂ ((algebraMap K L).comp O.subtype)
            (evTw ℓ z e'' e' (sg (Sum.inr j))) (f M j) ≠ 0) ∧
        ∑ s, vl ℓ (MvPolynomial.eval₂ ((algebraMap K L).comp O₀.subtype)
            (evTw ℓ z e'' e' (sg (Sum.inl s))) (F M s)) ≤
          (if ℓ = 2 then 1 else 0) * (Fintype.card Sig : ℝ) + ε ∧
        (∃ εj : JJ → ℝ, (∀ j, 0 ≤ εj j) ∧ ∑ j, εj j ≤ ε ∧
          ∀ j, vl ℓ (MvPolynomial.eval₂ ((algebraMap K L).comp O.subtype)
            (evTw ℓ z e'' e' (sg (Sum.inr j))) (f M j)) ≤ vv j + εj j) ∧
        2 * (t : ℝ) * ∑ i, (vl ℓ (z ^ (ℓ ^ e'' i) - 1) + vl ℓ (z ^ (ℓ ^ e' i) - 1)) ≤ ε

end Formalism.CyclotomicNorms
