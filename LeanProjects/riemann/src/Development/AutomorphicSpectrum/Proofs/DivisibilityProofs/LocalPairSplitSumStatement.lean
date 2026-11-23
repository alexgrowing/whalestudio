import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.LocalPairSplitSum
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_pair_split_sum : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (j j' : ℕ) (T : LocPair ι O (Fin (j + j'))) (P : Ideal (MRing ι O)) (k : ℕ) (Q : List (K → ℤ)), T.ck P k Q = (T.comp (Fin.castAdd j')).ck P k Q + (T.comp (Fin.natAdd j)).ck P k Q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.CkAppend.ck_append | exact GlobalTheory.CompanionTheory.Ar.Num.CkAppend.ck_append | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.CkAppend.ck_append <;> assumption)
