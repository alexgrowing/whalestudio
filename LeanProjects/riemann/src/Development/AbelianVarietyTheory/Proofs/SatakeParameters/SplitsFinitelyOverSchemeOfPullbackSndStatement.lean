import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitsFinitelyOverSchemeOfPullbackSnd
import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FibrePointsLEId
open CategoryTheory Limits AlgebraicGeometry
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitsFinitelyOverScheme_of_pullback_snd : ∀ {Z X S V : Scheme.{0}} (f : Z ⟶ X) (x : S ⟶ X) (v : V ⟶ S), GlobalTheory.EtC.Tr.Splits (pullback.snd f x) v → GlobalTheory.EtC.Tr.Splits f (v ≫ x) := by
  first | (exact @GlobalTheory.EtC.Tr.splits_of_splits_pullback_snd) | (exact GlobalTheory.EtC.Tr.splits_of_splits_pullback_snd) | (intros; apply GlobalTheory.EtC.Tr.splits_of_splits_pullback_snd  <;> assumption)
