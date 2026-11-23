import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaRecognitionLabelsAgreeOfIso
import Development.AbelianVarietyTheory.Definitions.Degenerations.NotAllMatchRankZero
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaRecognition_labels_agree_of_iso : AllMatch fun {_} _ {N} {N'} {_} μ _ _ => μ.A → ∀ J : NumD.Iso N N', μ.B J.e → μ.OnG J → (J.lam : _) = μ.c₀ → μ.OnQ J := by
  first | exact @GlobalTheory.LabelsAgree.main | exact GlobalTheory.LabelsAgree.main | (intros; apply GlobalTheory.LabelsAgree.main <;> assumption)
