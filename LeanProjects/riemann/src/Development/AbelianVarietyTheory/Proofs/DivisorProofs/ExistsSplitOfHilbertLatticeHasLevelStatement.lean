import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitOfHilbertLatticeHasLevel
import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_split_of_hilbertLatticeHasLevel : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (N : ℕ) (L : Lat F), 0 < N → HasLevel N L → ∃ (𝔞 𝔟 : Frac F) (x : F), L = split 𝔞 𝔟 x := by
  first | exact @GlobalTheory.HilbFam.exists_eq_split_of_hasLevel | exact GlobalTheory.HilbFam.exists_eq_split_of_hasLevel | (intros; apply GlobalTheory.HilbFam.exists_eq_split_of_hasLevel <;> assumption)
