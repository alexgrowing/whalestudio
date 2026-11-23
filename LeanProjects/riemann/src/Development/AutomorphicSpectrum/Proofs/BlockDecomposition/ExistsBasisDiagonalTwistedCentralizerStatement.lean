import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsBasisDiagonalTwistedCentralizer
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousConjNilSymm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableNilrad
open Matrix MeasureTheory PositivityTheory.Rg.BcB PositivityTheory.Rg.Tf.Loc GlobalTheory.CompanionTheory.LocVan
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_basis_diagonal_twisted_centralizer : ∀ (n : ℕ) (d : GL (Fin n) ℂ) (W₁ W₂ : Submodule ℂ (Fin n → ℂ)),
  (d * thC n d).val.charpoly.Separable → W₁ ≤ W₂ →
  perpD (starRingEnd ℂ) d W₁ = W₂ → perpD (starRingEnd ℂ) d W₂ = W₁ →
  ∃ P : GL (Fin n) ℂ,
    (∀ t ∈ twCent (thC n) d, ∃ a : Fin n → ℂ, (P⁻¹ * t * P).val = Matrix.diagonal a) ∧
    (∀ X ∈ nilrad W₁ W₂, ∀ i, ((P⁻¹ : GL (Fin n) ℂ).val * X * P.val) i i = 0) ∧
    (∀ t ∈ twCent (thC n) d, img t W₁ = W₁ ∧ img t W₂ = W₂) := by
  first | exact @GlobalTheory.CompanionTheory.LocVan.Frame.eigenframe | exact GlobalTheory.CompanionTheory.LocVan.Frame.eigenframe | (intros; apply GlobalTheory.CompanionTheory.LocVan.Frame.eigenframe <;> assumption)
