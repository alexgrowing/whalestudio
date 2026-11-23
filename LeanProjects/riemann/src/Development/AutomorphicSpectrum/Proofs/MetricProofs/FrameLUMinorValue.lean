import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsBaseChart
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogPeriodStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockDiagonalMinorVanishing
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LowerUnipotentMinorFormulaStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FrameMinorValueFormulaStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WMan.LowRead

theorem isProperStep_stepOf {N j : ℕ} (hj : j ≤ N) {a' b' : Fin N} (hba : b' < a')
    (hs : (a' : ℕ) < N - j ↔ (b' : ℕ) < N - j) : IsProperStep N j (stepOf N j b') := by
  have ha := a'.2
  have hb := b'.2
  have hba' : (b' : ℕ) < a' := hba
  simp only [IsProperStep, stepOf]
  split_ifs with h
  · constructor <;> omega
  · constructor <;> omega

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (zb : (Σ k, baseIdx ι M.blk k) → ℂ) (hh : Ψ → Matrix (Fin N) (Fin N) ℂ) (τ' : Ψ) (a' b' : Fin N) (z : (Σ k, ι k) → ℂ) (A L U : Matrix (Fin N) (Fin N) ℂ), M.IsFrame F → zb ∈ mcPts (mCoordIdeal M.x) → M.GoodAt F (mCoordIdeal zb) → IsBlockDiag j A → (hh τ')⁻¹ * A = L * U → IsBlockDiag j L → IsLowerUni L → IsBlockDiag j U → U.BlockTriangular id → (∀ c ∈ stepCols N j (stepOf N j b'), U c c ≠ 0) → b' < a' → ((a' : ℕ) < N - j ↔ (b' : ℕ) < N - j) → (∀ k, M.blk (τ', stepOf N j b') = some k → ∃ α : ℂ, α ≠ 0 ∧ ∀ m : ι k, z ⟨k, m⟩ = α * ∑ I, valAt M.x (F.u ⟨k, m⟩ I) zb * minorIJ A I (stepCols N j (stepOf N j b'))) → lowRead M F zb hh z τ' a' b' = L a' b' := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M F zb hh τ' a' b' z A L U hF hzb hG hA hLU hLb hLu hUb hUt hUd
    hba hs hz
  have hj := M.j_le
  have hP : IsProperStep N j (stepOf N j b') := isProperStep_stepOf hj hba hs
  obtain ⟨k, hk⟩ : ∃ k, M.blk (τ', stepOf N j b') = some k := by
    cases h : M.blk (τ', stepOf N j b') with
    | none => exact absurd hP ((M.blk_none _).1 h)
    | some k => exact ⟨k, rfl⟩
  obtain ⟨α, hα, hzα⟩ := hz k hk
  have hT : ∀ J, twMinor M F zb (stepOf N j b') k (hh τ')⁻¹ z J =
      α * (minorIJ L J (stepCols N j (stepOf N j b')) *
        minorIJ U (stepCols N j (stepOf N j b')) (stepCols N j (stepOf N j b'))) := by
    intro J
    rw [GlobalTheory.T.frame_minor_value_formula K ι Φ y Ψ N j M F zb (τ', stepOf N j b') k A (hh τ')⁻¹ z α J hF hzb hG hk
      hA hzα, hLU, MinorCalc.minorIJ_mul_of_support L U J (stepCols N j (stepOf N j b'))
      (MinorCalc.support_stepCols (i := stepOf N j b') hj U hUb hUt)]
  obtain ⟨h1, h2⟩ := GlobalTheory.T.lower_unipotent_minor_formula N j L a' b' hj hLb hLu hba hs
  have hUne : minorIJ U (stepCols N j (stepOf N j b')) (stepCols N j (stepOf N j b')) ≠ 0 := by
    rw [MinorCalc.minorIJ_self_of_triangular U hUt]
    exact Finset.prod_ne_zero_iff.2 hUd
  unfold lowRead
  simp only [hk, Option.elim_some]
  rw [hT, hT, h1, h2, one_mul, mul_div_mul_left _ _ hα, mul_div_assoc, div_self hUne, mul_one]

end GlobalTheory.CompanionTheory.Ar.PB.WMan.LowRead
