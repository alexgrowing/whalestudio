import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FractionRingAwayEtaleDedekindArtinianReduced
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fractionRing_away_etale_dedekind_artinian_reduced : ∀ (B : Type) [CommRing B] [IsDedekindDomain B] (f : B) (A' : Type) [CommRing A'] [Algebra B A'] [Algebra.Etale B A'], IsArtinianRing (FractionRing (Localization.Away (algebraMap B A' f))) ∧ IsReduced (FractionRing (Localization.Away (algebraMap B A' f))) := by
  first | (exact @GlobalTheory.fractionRing_away_etale_isArtinian_isReduced) | (exact GlobalTheory.fractionRing_away_etale_isArtinian_isReduced) | (intros; apply GlobalTheory.fractionRing_away_etale_isArtinian_isReduced <;> assumption)
