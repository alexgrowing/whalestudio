import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DefsMod

noncomputable section

open MvPolynomial Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

def ClosureBasicModules : Prop :=
  ∀ (n : ℕ) [NeZero n],
    (∀ M : GLMod n, Fintype.card M.ι = 1 → (∀ i j, M.A i j = 1) → Nonempty (ColFam M)) ∧
    (∀ (M : GLMod n) (mu : Fin n → ℤ) (β : M.ι → GLCoord ℤ n), Dominant mu → IsSMu M mu β → Nonempty (ColFam M)) ∧
    ∀ (M M' : GLMod n) (ε : ℤ), (ε = 1 ∨ ε = -1) → ∀ e : M'.ι ≃ M.ι,
      (∀ i j, M'.A i j = ((detU n ^ ε : (GLCoord ℤ n)ˣ) : GLCoord ℤ n) * M.A (e i) (e j)) →
      Nonempty (ColFam M) → Nonempty (ColFam M')

def ClosureTensorPowers : Prop :=
  ∀ (n : ℕ) [NeZero n] (M M' : GLMod n) (b : ℕ), Nonempty (ColFam M) →
    (∀ e, IsTensor M M' (SymMat n b) e → Nonempty (ColFam M')) ∧
    (∀ e, IsTensor M M' (SymDMat n b) e → Nonempty (ColFam M')) ∧
    (∀ e, IsTensor M M' (LamMat n b) e → Nonempty (ColFam M'))

def ClosureBranching : Prop :=
  ∀ (m : ℕ) [NeZero m] (M : GLMod (m + 1)) (lam : Fin (m + 1) → ℤ) (β : M.ι → GLCoord ℤ (m + 1)),
    Dominant lam → IsSMu M lam β →
    ∃ (Sg : Finset (Fin m → ℤ)) (ph : (nu : ↥Sg) → Matrix M.ι (TIdx (nu : Fin m → ℤ)) ℤ),
      (∀ nu : Fin m → ℤ, nu ∈ Sg ↔ Dominant nu ∧ Interl lam nu) ∧
      (∀ (nu : ↥Sg) (R : Type) [CommRing R] (h : GL (Fin (m + 1)) R) (g1 : GL (Fin m) R) (t : Rˣ), IsBlock h g1 t →
        M.A.map (evGL h) * (ph nu).map (Int.castRingHom R) =
          (((t ^ (∑ a, lam a - ∑ a, (nu : Fin m → ℤ) a) : Rˣ) : R)) • ((ph nu).map (Int.castRingHom R) *
            (TMat (nu : Fin m → ℤ)).map (evGL g1))) ∧
      (∀ nu : ↥Sg, (∀ (p : ℕ), p.Prime → (fun i => ((ph nu i (canT _) : ℤ) : ZMod p)) ≠ 0) ∧
        (fun i => ((ph nu i (canT _) : ℤ) : ℚ)) ≠ 0) ∧
      Fintype.card M.ι = ∑ nu : ↥Sg, dMu (nu : Fin m → ℤ)

end Formalism.InvariantFactorPaths.ColumnFamilies
