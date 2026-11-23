import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFundamentalDomainRationalUpperUnitriangula
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fundamentalDomain_rational_upperUnitriangular : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) [MeasurableSpace (GA E n)] [BorelSpace (GA E n)]
    (ν : Measure (GlobalTheory.CellDec.NA E n)) [ν.IsHaarMeasure], ∃ D : Set (GlobalTheory.CellDec.NA E n),
    IsFundamentalDomain ((GlobalTheory.CellDec.NE E n).subgroupOf (GlobalTheory.CellDec.NA E n)) D ν ∧ 0 < ν D ∧ ν D < ⊤ := by
  first | exact @GlobalTheory.CellDec.exists_fundamentalDomain_NE | exact GlobalTheory.CellDec.exists_fundamentalDomain_NE | (intros; apply GlobalTheory.CellDec.exists_fundamentalDomain_NE <;> assumption)
