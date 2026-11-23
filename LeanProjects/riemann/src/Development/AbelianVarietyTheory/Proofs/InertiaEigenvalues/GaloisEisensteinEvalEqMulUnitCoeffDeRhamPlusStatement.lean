import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisEisensteinEvalEqMulUnitCoeffDeRhamPlus
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanOfPowMul
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_eisensteinEval_eq_mul_unit_coeffDeRhamPlus : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [CompleteSpace K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (g : GQ l), g ∈ GK (ϖ.field a) → ∃ v : OD l O, IsUnit v ∧ GlobalTheory.GalStep.galOD O g (GlobalTheory.GalStep.ED K t ϖ) = GlobalTheory.GalStep.ED K t ϖ * v := by
  first | exact @GlobalTheory.GalStep.galOD_ED | exact GlobalTheory.GalStep.galOD_ED | (intros; apply GlobalTheory.GalStep.galOD_ED <;> assumption)
