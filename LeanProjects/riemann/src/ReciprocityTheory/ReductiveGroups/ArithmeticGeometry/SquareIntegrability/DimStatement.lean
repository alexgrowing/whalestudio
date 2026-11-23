import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ExistsPairs

namespace ReciprocityTheory.ChartRestriction.G.I2

open MeasureTheory Complex

noncomputable section

def DimStatement : Prop :=
  ∀ (ι : Type) [Fintype ι] (Y : GT ι) (q : ℕ), 1 ≤ q →
    FiniteDimensional ℂ (Y.Sec q) ∧ Module.finrank ℂ (Y.Sec q) ≤ q ^ Fintype.card ι

theorem dim : DimStatement :=
  fun _ _ Y q hq => DimC.dim_core Y q hq

end

end ReciprocityTheory.ChartRestriction.G.I2
