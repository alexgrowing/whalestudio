import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicModelOfDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
open GlobalTheory.LatVal GlobalTheory.LatJet
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraic_model_of_de_rham : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal → ModelAlg := by
  first | exact @GlobalTheory.ModelAlgProof.modelAlg | exact GlobalTheory.ModelAlgProof.modelAlg | (intros; apply GlobalTheory.ModelAlgProof.modelAlg <;> assumption)
