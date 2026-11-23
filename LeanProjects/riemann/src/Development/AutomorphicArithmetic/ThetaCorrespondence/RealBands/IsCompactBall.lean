import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.DecaysZero
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.RightDerivativeZeroOutsideSupport

open MeasureTheory Filter Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.FlagMeas GlobalTheory.RealInd UpperTheory.Lit.Cusp
open GlobalTheory.Dec (IsHaarSub IsIsoC NW IsSqIntIrr)
open scoped Topology InnerProductSpace

theorem UpperTheory.Lit.Cusp.isCompact_ball :
    ∀ (n : ℕ) (ε : Fin n → Bool), (∀ R : ℝ, IsCompact {g : UJ ε | hs (umat g) ≤ R}) ∧
      (∀ x y : Matrix (Fin n) (Fin n) ℂ, Real.sqrt (hs (x * y)) ≤ Real.sqrt (hs x) * Real.sqrt (hs y)) ∧
      (∀ g : UJ ε, hs (umat g⁻¹) = hs (umat g)) ∧ Continuous (fun g : UJ ε => hs (umat g)) := by
  intro n ε
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro R
    obtain ⟨hemb, -⟩ := isClosedEmbeddingMatrix n ε
    have hK := (hermitian_small_ball n ε).1 R
    have hpre := hemb.isCompact_preimage hK
    convert hpre using 1
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_preimage]
    constructor
    · intro h
      exact ⟨g.2, h⟩
    · intro h
      exact h.2
  · intro x y
    rw [← Real.sqrt_mul (frobenius_nonneg x)]
    exact Real.sqrt_le_sqrt (frobenius_mul_le x y)
  · intro g
    have h1 : umat g⁻¹ = Jm ε * (coeMatrixAlt ε g)ᴴ * Jm ε := coeMatrix_inv_eq ε g
    have h2 : coeMatrixAlt ε g = umat g := rfl
    rw [h1, h2]
    have hd : ∀ i, ‖(if ε i = true then (1 : ℂ) else -1)‖ = 1 := by
      intro i
      split <;> simp
    simp only [hs, Jm, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.conjTranspose_apply, norm_mul, hd,
      one_mul, mul_one, norm_star]
    exact Finset.sum_comm
  · exact continuous_hs_real_place_taylor.comp (continuous_coeMatrix ε)
