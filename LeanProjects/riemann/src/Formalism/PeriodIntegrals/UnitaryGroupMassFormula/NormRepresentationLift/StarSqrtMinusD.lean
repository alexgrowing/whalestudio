import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationLift.NormRepStepOfTrace
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.DiscrB

noncomputable section

open scoped Classical ComplexConjugate

namespace PI.NRL

open NumberField Formalism.BasicNotions Formalism.FrobeniusOrbits Polynomial

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem star_emb (D : D7) (x : D.host.E) : D.host.φ₀ (star x) = conj (D.host.φ₀ x) := by
  haveI := D.host.isCMField_hostE
  show D.host.φ₀ (NumberField.IsCMField.complexConj D.host.E x) = _
  exact NumberField.IsCMField.complexEmbedding_complexConj D.host.E D.host.φ₀ x

theorem star_sqrtMinusD (D : D7) : star D.host.sqrtMinusD = -D.host.sqrtMinusD := by
  apply D.host.φ₀.injective
  have h : D.host.φ₀ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) := D.host.φ₀_mem
  rw [star_emb, map_neg, h, map_mul, Complex.conj_I, Complex.conj_ofReal]
  ring

theorem traceOne (D : D7) : TraceOne D := by
  have hd : D.host.d % 16 = 7 := D.host.hyp.2.2.2.1
  obtain ⟨k, hk⟩ : ∃ k : ℕ, D.host.d + 1 = 4 * k := ⟨(D.host.d + 1) / 4, by omega⟩
  have hs : D.host.sqrtMinusD ^ 2 = -(D.host.d : D.host.E) := D.host.sqd_sq
  have hk' : (D.host.d : D.host.E) + 1 = 4 * (k : D.host.E) := by exact_mod_cast hk
  have hω : ((1 + D.host.sqrtMinusD) / 2) ^ 2 - (1 + D.host.sqrtMinusD) / 2 + (k : D.host.E) = 0 := by
    linear_combination (1 / 4 : D.host.E) * hs - (1 / 4 : D.host.E) * hk'
  have hint : IsIntegral ℤ ((1 + D.host.sqrtMinusD) / 2) := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (k : ℤ), by monicity!, ?_⟩
    simpa using hω
  refine ⟨⟨(1 + D.host.sqrtMinusD) / 2, hint⟩, ?_⟩
  show (1 + D.host.sqrtMinusD) / 2 + star ((1 + D.host.sqrtMinusD) / 2) = 1
  rw [star_div₀, star_add, star_one, star_sqrtMinusD, star_ofNat]
  ring

end PI.NRL
