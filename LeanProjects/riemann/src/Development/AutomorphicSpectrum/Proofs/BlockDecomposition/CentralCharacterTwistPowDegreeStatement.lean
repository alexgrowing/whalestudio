import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralCharacterTwistPowDegree
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CentredSegments.IrreducibleUnif
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.TemperedProducts.CentredSegSqInt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.StandardFunctorsFiniteLength
open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.central_character_twist_pow_degree : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (x : IrrGL k) (t : kˣ) (c s : ℂ), Zl.ScalarBy x t c → Zl.ScalarBy (x.nu s) t (c * ((absPow k s t : ℂˣ) : ℂ) ^ x.1) := by
  first | exact @GlobalTheory.CompanionTheory.ScalarTwist.scalarBy_nu | exact GlobalTheory.CompanionTheory.ScalarTwist.scalarBy_nu | (intros; apply GlobalTheory.CompanionTheory.ScalarTwist.scalarBy_nu <;> assumption)
