import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WhittakerFunctionalEquationAdditive
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GodementJacquetMinusOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PhdEqPhk
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerTemperedBoundDetOne
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.GJTwo.WhitBound

section L

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem modulus_add_le_max (a b : F) : modulus (a + b) ≤ max (modulus a) (modulus b) := by
  wlog h : modulus b ≤ modulus a generalizing a b
  · have := this b a (le_of_not_ge h)
    rwa [add_comm, max_comm]
  by_cases ha : a = 0
  · have hb : b = 0 := by
      rw [ha, modulus_zero] at h
      simpa using h
    simp [ha, hb]
  have hpos := modulus_pos ha
  have hq : b / a ∈ 𝒪[F] := by
    rw [← modulus_le_one_iff, div_eq_mul_inv, modulus_mul, modulus_inv]
    exact mul_inv_le_one_of_le₀ h (le_of_lt hpos)
  have h1 : 1 + b / a ∈ 𝒪[F] := add_mem (one_mem _) hq
  have h2 := (modulus_le_one_iff).2 h1
  have h3 : a + b = a * (1 + b / a) := by
    field_simp
  rw [h3, modulus_mul]
  exact le_max_of_le_left (mul_le_of_le_one_right zero_le h2)

theorem modulus_neg_le (x : F) : modulus (-x) ≤ modulus x := by
  have h : modulus (-1 : F) ≤ 1 := (modulus_le_one_iff).2 (neg_mem (one_mem _))
  have e : -x = (-1) * x := by ring
  rw [e, modulus_mul]
  exact mul_le_of_le_one_left zero_le h

end L

end GlobalTheory.CompanionTheory.GJTwo.WhitBound
