import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsotropicOutsideLine
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.DiscrMulHermitianIntegral

namespace ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem unipotent_lattice_lift : UnipotentLatticeLift (E := E) := by
  intro r X u hu hmem
  exact ⟨fun b hb => X.exists_gamma u hu hmem b hb,
    fun la P hP hχ b hb x hx => X.LZ_periodic u hu hmem la P hP hχ b hb x hx,
    fun χ hχ hf => X.freq_to_beta χ hχ hf⟩

end ReciprocityTheory.ChartRestriction.G.FD
