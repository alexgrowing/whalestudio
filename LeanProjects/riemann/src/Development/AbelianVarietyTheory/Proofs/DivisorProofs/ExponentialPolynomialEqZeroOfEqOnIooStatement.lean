import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExponentialPolynomialEqZeroOfEqOnIoo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemExpSolCons
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exponentialPolynomial_eq_zero_of_eqOn_Ioo : ∀ (l : List ℂ) (f : ℝ → ℂ), f ∈ expSol l → ∀ s t : ℝ, s < t → (∀ x ∈ Set.Ioo s t, f x = 0) → f = 0 := by
  first | exact @GlobalTheory.HCF.expSol_eq_zero_of_eqOn_Ioo | exact GlobalTheory.HCF.expSol_eq_zero_of_eqOn_Ioo | (intros; apply GlobalTheory.HCF.expSol_eq_zero_of_eqOn_Ioo <;> assumption)
