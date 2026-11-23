import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ScaledIntegerPeriodic
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwasawaStdMaxParab
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit

namespace GlobalTheory.IndSpK

theorem eq_zero_of_KO_invariant_of_apply_one : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (a a' : ℕ) (α β : kˣ →* ℂˣ), ∀ f ∈ indSp a a' α β,
    (∀ u ∈ KO k (Fin (a + a')), ∀ h, f (h * u) = f h) → f 1 = 0 → f = 0 := by
  intro k _ _ _ _ a a' α β f hf hK h1
  funext g
  obtain ⟨p, hp, κ, hκ, rfl⟩ := (GlobalTheory.MaxParabIwasawa.iwasawa_stdMaxParab k (a + a') a a' rfl g).2
  rw [Pi.zero_apply, hK κ hκ p]
  rw [GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic.mem_stdMaxParab] at hp
  set M := p.val.submatrix finSumFinEquiv finSumFinEquiv with hM
  have h21 : M.toBlocks₂₁ = 0 := by
    ext i j
    simp only [hM, Matrix.toBlocks₂₁, Matrix.of_apply, Matrix.submatrix_apply, Matrix.zero_apply]
    exact hp _ _ (by simp) (by simp)
  have hdet : M.det = M.toBlocks₁₁.det * M.toBlocks₂₂.det := by
    rw [← Matrix.fromBlocks_toBlocks M, h21, Matrix.det_fromBlocks_zero₂₁]
    simp
  have hMdet : M.det ≠ 0 := by
    rw [hM, Matrix.det_submatrix_equiv_self]
    exact p.isUnit.map Matrix.detMonoidHom |>.ne_zero
  rw [hdet] at hMdet
  have hA : M.toBlocks₁₁.det ≠ 0 := left_ne_zero_of_mul hMdet
  have hD : M.toBlocks₂₂.det ≠ 0 := right_ne_zero_of_mul hMdet
  have hb : p.val.submatrix finSumFinEquiv finSumFinEquiv =
      fromBlocks (GeneralLinearGroup.mkOfDetNeZero _ hA).val M.toBlocks₁₂ 0
        (GeneralLinearGroup.mkOfDetNeZero _ hD).val := by
    rw [← h21]
    exact (Matrix.fromBlocks_toBlocks M).symm
  have := hf.1 p _ _ _ hb 1
  rw [mul_one] at this
  rw [this, h1, mul_zero]

end GlobalTheory.IndSpK
