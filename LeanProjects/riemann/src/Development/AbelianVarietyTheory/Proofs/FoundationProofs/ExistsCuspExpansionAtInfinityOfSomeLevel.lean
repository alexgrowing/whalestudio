import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCuspExpansionDiscriminantIntegerLeadingOneStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsCuspExpansionAtInfinityPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FnHahnSeriesOfHasQStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem exists_isExp : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ) (f : ℍ → ℂ), InR ε.range f →
    ∃ h : HahnSeries ℚ Ω, IsExp ε f h := by
  intro Ω _ ε f hf
  obtain ⟨N, w, hN, -, hq⟩ := hf
  obtain ⟨a, ha, hmem⟩ := hq 1
  choose b hb using fun n => (hmem n : a n ∈ ε.range)
  have hg : HasQ N (fun τ => DD τ ^ w * f τ) (fun n => ε (b n)) := by
    intro τ
    have := ha τ
    simp only [one_smul] at this
    simpa only [hb] using this
  obtain ⟨hg', hexg, -, -⟩ := GlobalTheory.T.exists_hahnSeries_isExp_of_hasQ Ω ε N _ b hN hg
  obtain ⟨hD, hexD, hD0, -, -⟩ := GlobalTheory.T.exists_cuspExpansion_discriminant_integer_leading_one Ω ε
  obtain ⟨hring, -, hconst, -, hinv⟩ := GlobalTheory.T.isCuspExpansionAtInfinity_properties Ω ε
  have hDi := hinv DD hD hD0 hexD
  have hpow : ∀ k : ℕ, IsExp ε (DD⁻¹ ^ k) (hD⁻¹ ^ k) := by
    intro k
    induction k with
    | zero =>
      have := hconst 1
      simp only [map_one, HahnSeries.C_one] at this
      rw [pow_zero, pow_zero]
      exact this
    | succ k ih =>
      simpa [pow_succ] using (hring _ _ _ _ ih hDi).2.2
  have hprod := (hring _ _ _ _ hexg (hpow w)).2.2
  refine ⟨hg' * hD⁻¹ ^ w, ?_⟩
  convert hprod using 1
  funext τ
  have := ReciprocityTheory.ChartRestriction.L1.DD_ne_zero τ
  simp only [Pi.mul_apply, Pi.pow_apply, Pi.inv_apply]
  rw [inv_pow, mul_comm (DD τ ^ w), mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ this), mul_one]

end GlobalTheory.FN
