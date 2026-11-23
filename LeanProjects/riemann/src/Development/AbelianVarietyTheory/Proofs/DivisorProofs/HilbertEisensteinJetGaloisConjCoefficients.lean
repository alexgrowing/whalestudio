import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHilbertEisensteinFourierCoeffFamilyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinSeriesRingEquivConjStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutEmbInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasQExpansionOfLevelHilbertEisensteinQuasiPeriodStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitOfHilbertLatticeHasLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertSplitLatticeTwistDiagonalCoprimeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertLatticeTwistHasLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialZetaConstTermEqRationalValue

set_option autoImplicit false

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)

namespace GlobalTheory.HilbFam

theorem qConj_hfun_twist : EisExp → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F → ∀ (s N : ℕ) (L : Lat F), 1 ≤ s → 0 < N → HasLevel N L → ∀ (z : ClassGroup (𝓞 F) → ℚ), ZetaVals (2 * s) z → ∀ (g : ℂ ≃+* ℂ) (m : ℤ) (κ κ' : Emb F → ℕ) (Ch Ch' : ℍ → ℂ), IsCoprime m (N : ℤ) → g (Complex.exp ((2 * Real.pi * Complex.I) / N)) = Complex.exp ((2 * Real.pi * Complex.I) * m / N) → (∀ i j : Emb F, (∀ y : F, g ((i y : ℝ) : ℂ) = ((j y : ℝ) : ℂ)) → κ' j = κ i) → QConj g N Ch Ch' → QConj g N (hfun (2 * s) L κ Ch) (hfun (2 * s) (twist N L (Matrix.diagonal ![1, (m : ZMod N)])) κ' Ch') := by
  intro hE F _ _ _ hf s N L hs hN hL z hz g m κ κ' Ch Ch' hm hg hκ hC
  obtain ⟨𝔞, 𝔟, x, rfl⟩ := exists_eq_split_of_hasLevel F N L hN hL
  have htw := GlobalTheory.T.hilbertSplitLattice_twist_diagonal_coprime F N 𝔞 𝔟 x m hm hL
  have hL' := hasLevel_twist_of_hasLevel F N _ (Matrix.diagonal ![1, (m : ZMod N)]) hL
  rw [htw] at hL' ⊢
  obtain ⟨Z, a, hZ, ha⟩ := GlobalTheory.T.exists_hilbertEisenstein_fourierCoeffFamily hE F hf 𝔞 𝔟 s hs
  have h0 := constTerm_eq_zetaVal F (2 * s) z _ Z (by omega) hz hZ
  obtain ⟨π, hπ⟩ := aut_perm_emb F g
  have hκ' : κ' = fun j ↦ κ (π.symm j) := by
    funext j
    refine hκ (π.symm j) j fun y ↦ ?_
    rw [hπ, Equiv.apply_symm_apply]
  obtain ⟨c, hc, hc'⟩ := hC
  have hev : Even (2 * s) := even_two_mul s
  refine ⟨_, GlobalTheory.T.hasQExpansionOfLevel_hilbertEisensteinQuasiPeriodJet F (2 * s) 𝔞 𝔟 _ a x N κ Ch c hN hev ha hL hc, ?_⟩
  have h2 := GlobalTheory.T.hasQExpansionOfLevel_hilbertEisensteinQuasiPeriodJet F (2 * s) 𝔞 𝔟 _ a (m * x) N κ' Ch' _ hN hev ha hL' hc'
  have h3 := fun n ↦ GlobalTheory.T.hilbertEisensteinSeries_ringEquiv_conj F (2 * s) 𝔞 𝔟 _ a x s N g m π κ c n rfl hN ha
    (by rw [h0, map_ratCast]) hL hg hπ
  simp only [h3]
  rw [hκ'] at h2 ⊢
  exact h2

end GlobalTheory.HilbFam
