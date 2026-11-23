import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MinorRatioRegularOfInvertible
import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordTieCompEquiv
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.minor_ratio_regular_of_invertible : ∀ (K : Type) [Field K] (R : Subring K) (n r : ℕ) (A : Matrix (Fin n) (Fin r) K) (B : Matrix (Fin r) (Fin n) K) (G : Matrix (Fin r) (Fin r) K) (a : K) (k : Fin r) (J : Fin ((k : ℕ) + 1) → Fin n), (∀ j l, A j l ∈ R) → (∀ l j, B l j ∈ R) → B * A = 1 → a ≠ 0 → ((a • (A * G)).submatrix J (Fin.castLE k.2)).det ≠ 0 → (∀ l j, ((a • (A * G)).submatrix (Function.update J l j) (Fin.castLE k.2)).det / ((a • (A * G)).submatrix J (Fin.castLE k.2)).det ∈ R) → ∃ D Ee : Fin ((k : ℕ) + 1) → Fin r → K, (∀ l i, D l i ∈ R) ∧ (∀ l i, Ee l i ∈ R) ∧ (∀ l l', ∑ i, Ee l i * D l' i = if l = l' then 1 else 0) ∧ ∀ l, D l ∈ flagStep K (fun c i => G i c) ((k : ℕ) + 1) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagBun.split_of_regular_ratios | exact GlobalTheory.CompanionTheory.Ar.FlagBun.split_of_regular_ratios | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagBun.split_of_regular_ratios <;> assumption)
