import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousGlobalWhittakerCoefficientArchimedean
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_globalWhittakerCoefficient_archimedean : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (φ : Sm E a), IsAutForm φ → ∀ g h : GA E a, Continuous (fun y : GL (Fin a) (Cinf E) => GlobalTheory.JSW.whit φ.1 (g * infGL E a y * h)) := by
  first | exact @GlobalTheory.JSW.continuous_whit_infGL | exact GlobalTheory.JSW.continuous_whit_infGL | (intros; apply GlobalTheory.JSW.continuous_whit_infGL <;> assumption)
