import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHilbertEisensteinLatticeValueOfEisensteinSerieStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinFourierExpansionSupportStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinLatticeValueEqOfIsValueStatement

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)

namespace GlobalTheory.HilbFam

theorem exists_isCoef : EisExp → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F → ∀ (𝔞 𝔟 : Frac F) (s : ℕ), 1 ≤ s → ∃ (Z : ℂ → ℂ) (a : F → ℂ), IsPartialZeta (ClassGroup.mk F 𝔞)⁻¹ Z ∧ IsCoef (2 * s) 𝔞 𝔟 ((2 : ℂ)⁻¹ ^ Module.finrank ℚ F * Z (1 - ((2 * s : ℕ) : ℂ))) a := by
  intro hE F _ _ _ hf 𝔞 𝔟 s hs
  obtain ⟨G, hG, -, hX⟩ := hE F hf 𝔞 𝔟 s hs
  obtain ⟨Z, a, hZ, h0, hint, hsupp, hsum⟩ := GlobalTheory.T.hilbertEisenstein_fourier_expansion_support F (2 * s) 𝔞 𝔟 G hX
  refine ⟨Z, a, hZ, h0, hint, hsupp, fun w hw ↦ ?_⟩
  have hv := GlobalTheory.T.hilbertEisensteinLatticeValue_eq_of_isValue F (2 * s) _ _ _ _ (GlobalTheory.T.isHilbertEisensteinLatticeValue_of_eisensteinSeries F (2 * s) 𝔞 𝔟 G w (even_two_mul s) hG hw)
  have hne : ((2 * Real.pi * Complex.I : ℂ) ^ Module.finrank ℚ F) ^ (2 * s) ≠ 0 :=
    pow_ne_zero _ (pow_ne_zero _ Complex.two_pi_I_ne_zero)
  rw [hv, mul_pow ((2 * Real.pi * Complex.I : ℂ) ^ Module.finrank ℚ F), mul_left_comm, mul_div_mul_left _ _ hne]
  exact hsum w hw

end GlobalTheory.HilbFam
