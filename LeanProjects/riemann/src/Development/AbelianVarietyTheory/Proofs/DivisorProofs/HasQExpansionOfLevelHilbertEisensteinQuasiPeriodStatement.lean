import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasQExpansionOfLevelHilbertEisensteinQuasiPeriod
import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasQExpansionOfLevel_hilbertEisensteinQuasiPeriodJet : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (𝔞 𝔟 : Frac F) (a₀ : ℂ) (a : F → ℂ) (x : F) (N : ℕ) (κ : Emb F → ℕ) (Ch : ℍ → ℂ) (c : ℕ → ℂ), 0 < N → Even k → IsCoef k 𝔞 𝔟 a₀ a → HasLevel N (split 𝔞 𝔟 x) → HasQ N Ch c → HasQ N (hfun k (split 𝔞 𝔟 x) κ Ch) (fun n ↦ PowerSeries.coeff n (hser k N 𝔞 a x κ c)) := by
  first | exact @GlobalTheory.HilbFam.ExpH.hasQ_hfun | exact GlobalTheory.HilbFam.ExpH.hasQ_hfun | (intros; apply GlobalTheory.HilbFam.ExpH.hasQ_hfun <;> assumption)
