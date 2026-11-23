import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhiskerLeftLeftIsPullbackSnd
import Mathlib
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPullback_whiskerLeft_left_snd : ∀ (S : Scheme.{0}) (U T T' : Over S) (f : T' ⟶ T), IsPullback (U ◁ f).left (snd U T').left (snd U T).left f.left := by
  first | exact @GlobalTheory.whiskerLeft_left_isPullback_snd | exact GlobalTheory.whiskerLeft_left_isPullback_snd | (intros; apply GlobalTheory.whiskerLeft_left_isPullback_snd <;> assumption)
