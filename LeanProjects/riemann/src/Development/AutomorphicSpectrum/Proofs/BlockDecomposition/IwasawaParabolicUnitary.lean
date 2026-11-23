import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrderedCechToCatCochainsOneApplyValueAtSubset
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaUnitaryUpperTriangular
open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.ModelS

theorem exists_Pb_mul_unitary : ∀ (n : ℕ) (lev : Fin n → ℕ), Monotone lev → ∀ g ∈ GLs n,
    ∃ p ∈ GlobalTheory.CompanionTheory.ModelS.Pb lev, ∃ k : Matrix.unitaryGroup (Fin n) ℂ, g = p * k.1 := by
  intro n lev hlev g hg
  have hdet : g.det ≠ 0 := hg
  have hu : IsUnit gᴴ := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_conjTranspose]
    exact isUnit_iff_ne_zero.2 (by simpa using hdet)
  obtain ⟨k, hk, b, hb, ht⟩ := GlobalTheory.CompanionTheory.QR.exists_unitary_mul_blockTriangular gᴴ hu
  have hg' : g = bᴴ * kᴴ := by
    rw [← Matrix.conjTranspose_mul, ← hb, Matrix.conjTranspose_conjTranspose]
  have hkH : kᴴ ∈ Matrix.unitaryGroup (Fin n) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff]
    have := (Matrix.mem_unitaryGroup_iff').1 hk
    simpa [Matrix.star_eq_conjTranspose] using this
  refine ⟨bᴴ, ⟨?_, ?_⟩, ⟨kᴴ, hkH⟩, hg'⟩
  · intro h0
    apply hdet
    rw [hg', Matrix.det_mul]
    have h0' : (bᴴ).det = 0 := h0
    rw [h0', zero_mul]
  · intro a c hac
    have hlt : a < c := by
      by_contra hn
      exact absurd (hlev (not_lt.1 hn)) (not_le.2 hac)
    have : b c a = 0 := ht hlt
    simp [Matrix.conjTranspose_apply, this]

end GlobalTheory.CompanionTheory.ModelS
