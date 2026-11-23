import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinJetGaloisConjCoefficients
import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbert_eisenstein_jet_galois_conj_coefficients : EisExp → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F → ∀ (s N : ℕ) (L : Lat F), 1 ≤ s → 0 < N → HasLevel N L → ∀ (z : ClassGroup (𝓞 F) → ℚ), ZetaVals (2 * s) z → ∀ (g : ℂ ≃+* ℂ) (m : ℤ) (κ κ' : Emb F → ℕ) (Ch Ch' : ℍ → ℂ), IsCoprime m (N : ℤ) → g (Complex.exp ((2 * Real.pi * Complex.I) / N)) = Complex.exp ((2 * Real.pi * Complex.I) * m / N) → (∀ i j : Emb F, (∀ y : F, g ((i y : ℝ) : ℂ) = ((j y : ℝ) : ℂ)) → κ' j = κ i) → QConj g N Ch Ch' → QConj g N (hfun (2 * s) L κ Ch) (hfun (2 * s) (twist N L (Matrix.diagonal ![1, (m : ZMod N)])) κ' Ch') := by
  first | exact @GlobalTheory.HilbFam.qConj_hfun_twist | exact GlobalTheory.HilbFam.qConj_hfun_twist | (intros; apply GlobalTheory.HilbFam.qConj_hfun_twist <;> assumption)
