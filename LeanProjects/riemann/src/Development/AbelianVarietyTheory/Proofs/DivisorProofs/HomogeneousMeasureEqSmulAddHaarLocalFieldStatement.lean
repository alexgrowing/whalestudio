import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousMeasureEqSmulAddHaarLocalField
import Development.AbelianVarietyTheory.Definitions.Divisors.UnipVal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homogeneousMeasure_eq_smul_addHaar_localField : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (lam : Measure F) [lam.IsAddHaarMeasure] (n : Measure F) [IsFiniteMeasureOnCompacts n], n {0} = 0 → (∀ u : Fˣ, n.map (fun x => (u : F) * x) = (distribHaarChar F u)⁻¹ • n) → ∃ r : NNReal, n = r • lam := by
  first | exact @GlobalTheory.KSp.Homog.eq_smul_haar_of_homog | exact GlobalTheory.KSp.Homog.eq_smul_haar_of_homog | (intros; apply GlobalTheory.KSp.Homog.eq_smul_haar_of_homog <;> assumption)
