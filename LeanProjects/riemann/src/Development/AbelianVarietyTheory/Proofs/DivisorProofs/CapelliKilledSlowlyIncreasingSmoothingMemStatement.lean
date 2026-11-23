import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CapelliKilledSlowlyIncreasingSmoothingMem
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemKilled
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealLieSmoothingMemSmoothAdelicFunctionsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieDerivativeRealLieSmoothingEqDensityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealLieSmoothingMemSlowlyIncreasingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentreEnvelopingAlgebraCommuteRealLieSmoothingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothingRightTranslateMaxCompactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FundamentalDomainMeasureFinite
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.capelliKilled_slowlyIncreasing_smoothing_mem : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (b : ℕ) (ν : Measure (Lie E b)) [ν.IsAddHaarMeasure] (α : Lie E b → ℂ), IsTest (invSet E b) α → KInv α → ∀ (L : Subgroup (GL (Fin b) (Af E))) (W : Submodule ℂ (Kinf E b → ℂ)), FiniteDimensional ℂ W → ∀ (q : (E →+* ℂ) → ℂ → Polynomial ℂ) (ψ : Sm E b), ψ ∈ leftInv E b ⊓ fixL E b L ⊓ GlobalTheory.CapKilled.ktype E b W ⊓ GlobalTheory.CapKilled.killed E b q → ψ.1 ∈ growth E b → ∃ h : smoothing ν α ψ.1 ∈ Sm E b, (⟨smoothing ν α ψ.1, h⟩ : Sm E b) ∈ GlobalTheory.CapKilled.space E b L W q := by
  first | exact @GlobalTheory.CapKilledSmooth.smoothing_mem_space | exact GlobalTheory.CapKilledSmooth.smoothing_mem_space | (intros; apply GlobalTheory.CapKilledSmooth.smoothing_mem_space <;> assumption)
