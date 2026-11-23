import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsModularFormLevelOneOfInvariantQExpansion
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModEvalMF
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasQExpansionOfLevelMulLevelSubstPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasQExpansionOfLevelCoeffAndFunctionUniqueStatement

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)

namespace GlobalTheory.QFam

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in
open ModularForm (E₄ E₆) in

theorem _root_.GlobalTheory.QFam.exists_eq_DD_pow_mul_eval_jT : ∀ (R : Subring ℂ) (N w : ℕ)
    (f : ℍ → ℂ), 0 < N →
    (∀ γ : SL(2, ℤ), f ∣[(12 * w : ℤ)] γ = f) → _root_.GlobalTheory.QFam.QAll (· ∈ R) N f →
    ∃ P : Polynomial ℂ, (∀ i, P.coeff i ∈ R) ∧ ∀ τ, f τ = _root_.ReciprocityTheory.ChartRestriction.L1.DD τ ^ w * P.eval (_root_.ReciprocityTheory.ChartRestriction.L1.jT τ) := by
  intro R N w f hN hinv hq
  obtain ⟨a, ha, haR⟩ := hq
  have hmf : _root_.ReciprocityTheory.ChartRestriction.L1.IsMF (12 * w) f := _root_.GlobalTheory.QFam.isMF_of_invariant_of_hasQ N _ f a hN hinv ha
  have h1 : _root_.GlobalTheory.QFam.HasQ 1 f fun n => PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 f) := by
    rw [_root_.GlobalTheory.QFam.hasQ_coeff_iff_hasQExpansion]
    obtain ⟨g, hg⟩ := hmf
    have hgf : (⇑g : ℍ → ℂ) = f := funext hg
    have h := _root_.GlobalTheory.hasQExpansion_modularForm g
    rw [hgf] at h
    simpa using h
  have hN' := _root_.GlobalTheory.QFam.hasQ_mul_spread 1 N f _ one_pos hN h1
  rw [one_mul] at hN'
  have heq := _root_.GlobalTheory.QFam.HasQ.coeff_unique hN ha hN'
  have hcoeff : _root_.ReciprocityTheory.ChartRestriction.L1.CoeffIn R (UpperHalfPlane.qExpansion 1 f) := by
    intro m
    have h := haR (N * m)
    rw [heq] at h
    simpa [_root_.GlobalTheory.QFam.spread, Nat.mul_div_cancel_left _ hN] using h
  obtain ⟨P, hPR, -, hP⟩ := _root_.ReciprocityTheory.ChartRestriction.L1.qPrin R w f hmf hcoeff
  exact ⟨P, hPR, hP⟩

end GlobalTheory.QFam
