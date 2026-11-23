import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HaarInfiniteGLLtTopOfInfiniteGLHaarMeasureLtTop
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteVolumeAdelicUnitaryQuotient
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdeleClassFiniteness.BorelGL
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdeleClassFiniteness.LatticeIdealNonzero

open NumberField IsDedekindDomain Matrix MeasureTheory Topology
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haar_infiniteGL_lt_top_of_infiniteGLHaarMeasure_lt_top : ∀ (E : Type) [Field E] [NumberField E] (j : ℕ) [MeasurableSpace (GL (Fin j) (Cinf E))] [BorelSpace (GL (Fin j) (Cinf E))] (ν : Measure (GL (Fin j) (Cinf E))) [ν.IsHaarMeasure] (D : Set (GlobalTheory.FlagMeas.MatInf E j)), MeasurableSet D → GlobalTheory.FlagMeas.haarGL E j D < ⊤ → ν {y | (fun w a b => (y : Matrix (Fin j) (Fin j) (Cinf E)) a b w : GlobalTheory.FlagMeas.MatInf E j) ∈ D} < ⊤ := by
  first | exact @GlobalTheory.haarGL_finite_pullback | exact GlobalTheory.haarGL_finite_pullback | (intros; apply GlobalTheory.haarGL_finite_pullback <;> assumption)
