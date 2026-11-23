import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PoleLengthBound.ColDeriv
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PoleLengthBound.UnitCols
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BaseLengthBound.TaylorHasse
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BaseLengthBound.Column

noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.EtaleWeightGaps

namespace PI.PoleLengthCount

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}

theorem column_derivative (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) : ColDeriv G la :=
  colDeriv_of PoleLengthBounds.taylorHasse_holds G la

theorem unit_columns_holds (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (Q : LocalPointData G la)
    (S : Scal B) (CRm : ℝ) (T : ℕ) (c : ℝ) (hOk : Q.Ok S CRm T c) (hw : ∀ k, G.w k ∈ X.WWc S.sW wL) :
    UnitCols G la :=
  unitCols_of_column PoleLengthBounds.column_holds G la Q S CRm T c hOk hw

end PI.PoleLengthCount
