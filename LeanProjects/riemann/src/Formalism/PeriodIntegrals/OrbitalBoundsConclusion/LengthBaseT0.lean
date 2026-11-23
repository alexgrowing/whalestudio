import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BaseLengthBound.LenBaseHolds

theorem length_base_t0 : ∀ {D : Formalism.BasicNotions.D7} {B : Formalism.MainNotions.WeightFamilies.Prov D} {P : Formalism.MainNotions.ModuliIntegralCharts.Prov D} {j : ℕ}
    {X : Formalism.MainNotions.WeightAlgebra.PJ D B P j} {ka wL wF : Formalism.MainNotions.WeightFamilies.Wt D j},
    Formalism.MainNotions.Gaps.EtaleWeightGaps.LenBase (X := X) (ka := ka) (wL := wL) (wF := wF) :=
  PoleLengthBounds.lenBase_holds
