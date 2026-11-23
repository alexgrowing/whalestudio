import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.SecondPropositionEveryLocalisation
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.NoThreeConsecutiveThickPlaces
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.GenericFramesLetters
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.BranchingInterlacingPairs
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.PointsPropertyOfD7
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.DroppingPropositionHolds
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.RamificationTwoAndConjugationAtQAndD
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.LemmaOneEightOfPolarisation
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.LemmaOneEightOfDifferent
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.LemmaOneEightHolds

namespace Formalism.MainNotions.UnusedSlot33

open Formalism.BasicNotions

theorem field_lemmas_two_to_six (D : D7) (sc : Scale) :
    Conclusion2 D ∧ PointsLemma D ∧ Conclusion4 D 100 ∧ TorusPairsWithVariant D ∧ Conclusion6 D sc :=
  ⟨second_proposition_every_localisation D, points_property_of_d7 D, generic_frames_letters D, no_three_consecutive_thick_places D, branching_interlacing_pairs D sc⟩

theorem field_lemmas_except_seven : ∃ C₅ : ℝ, ∀ (D : D7) (sc : Scale),
    Conclusion1 D ∧ Conclusion2 D ∧ PointsLemma D ∧ Conclusion4 D 100 ∧ Conclusion5 D C₅ ∧ TorusPairsWithVariant D ∧ Conclusion6 D sc ∧ Conclusion8 D := by
  obtain ⟨C, hC⟩ := dropping_proposition_holds
  refine ⟨C, fun D sc => ?_⟩
  obtain ⟨h2, h3, h4, h5c, h6⟩ := field_lemmas_two_to_six D sc
  exact ⟨ramification_two_and_conjugation_at_q_and_d D, h2, h3, h4, hC D, h5c, h6, lemma_one_eight_holds D⟩

end Formalism.MainNotions.UnusedSlot33
