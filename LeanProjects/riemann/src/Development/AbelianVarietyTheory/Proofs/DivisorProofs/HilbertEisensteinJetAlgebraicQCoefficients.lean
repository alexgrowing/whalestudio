import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertDiagonalRestrictionCoeffIsAlgebraicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHilbertEisensteinFourierCoeffFamilyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasQExpansionOfLevelHilbertEisensteinQuasiPeriodStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitOfHilbertLatticeHasLevelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialZetaConstTermEqRationalValueStatement
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)

namespace GlobalTheory.HilbFam

theorem qAll_isAlgebraic_hfun : EisExp → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F],
    2 ≤ Module.finrank ℚ F → ∀ (s N : ℕ) (L : Lat F), 1 ≤ s → 0 < N → HasLevel N L →
    ∀ (z : ClassGroup (𝓞 F) → ℚ), ZetaVals (2 * s) z → ∀ (κ : Emb F → ℕ) (Ch : ℍ → ℂ),
    QAll (IsAlgebraic ℚ) N Ch → QAll (IsAlgebraic ℚ) N (hfun (2 * s) L κ Ch) := by
  intro hE F _ _ _ hf s N L hs hN hL z hz κ Ch hCh
  obtain ⟨c, hc, halg⟩ := hCh
  obtain ⟨𝔞, 𝔟, x, rfl⟩ := GlobalTheory.T.exists_split_of_hilbertLatticeHasLevel F N L hN hL
  obtain ⟨Z, a, hZ, ha⟩ := GlobalTheory.T.exists_hilbertEisenstein_fourierCoeffFamily hE F hf 𝔞 𝔟 s hs
  have hconst := GlobalTheory.T.partialZeta_constTerm_eq_rational_value F (2 * s) z _ Z (by omega) hz hZ
  have ha₀ : IsAlgebraic ℚ ((2 : ℂ)⁻¹ ^ Module.finrank ℚ F * Z (1 - ((2 * s : ℕ) : ℂ))) := by
    rw [hconst]
    exact isAlgebraic_algebraMap (R := ℚ) (A := ℂ) _
  exact ⟨_, GlobalTheory.T.hasQExpansionOfLevel_hilbertEisensteinQuasiPeriodJet F (2 * s) 𝔞 𝔟 _ a x N κ Ch c hN (even_two_mul s) ha hL hc,
    fun n ↦ GlobalTheory.T.hilbertDiagonalRestriction_coeff_isAlgebraic F (2 * s) 𝔞 𝔟 _ a x s N κ c n rfl ha ha₀ halg⟩

end GlobalTheory.HilbFam
