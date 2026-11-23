import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmSkewIdealFractionalIdeal
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
open NumberField GlobalTheory.CMVal GlobalTheory.LatJet GlobalTheory.RealMult
open GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex (latMod polMod dualLat TrInt bar)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_skew_ideal_fractional_ideal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (M : Submodule (OF E) E) (ξ : E), ξ ≠ 0 → bar ξ = -ξ →
    (∀ m ∈ M, bar m = -m) → IsUnit M → ∃ 𝔠 : FracId (FR E), ∀ a : FR E, a ∈ 𝔠.elt ↔ (a : E) * ξ ∈ M := by
  first | exact @GlobalTheory.AntiInvFrac.fracId_of_antiInv | exact GlobalTheory.AntiInvFrac.fracId_of_antiInv | (intros; apply GlobalTheory.AntiInvFrac.fracId_of_antiInv <;> assumption)
