import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.WhatContinuous

namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField MeasureTheory

theorem zm_norm {E : Type} [Field E] [NumberField E] [IsCMField E] {X : PT E} {DF : ℕ} {P : Par X DF}
    {I : Submodule ℤ (Vsp X.dim)} (hI : IsSplit P I) (hP : Ext.PackingCount)
    {s : (Fin 1 → Vsp X.dim) → ℂ} (hs : s ∈ X.Sec 1 1) :
    |(Col.ob (IR I)).toBasis.det (ZM.Ib hI)| * (2 : ℝ) ^ (-(Module.finrank ℝ (IR I) : ℝ) / 2) *
      (Col.YB hI hP 1).l2 1 (ZM.zmB hI s) ≤ X.l2 1 s :=
  le_of_eq (ZM.zm_norm_eq hI hP hs).symm

end ReciprocityTheory.ChartRestriction.G.I2
