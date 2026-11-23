import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainExtension.PointAssembly.DivLeExpOfAbsLogSubLe
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainExtension.PointAssembly.Frames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainExtension.PointAssembly.FourierJacobiDifferentiable

open PIW.FdPA in
theorem fd_point_assembly {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] : ReciprocityTheory.ChartRestriction.G.FD.ShortVectorBound (E := E) → ReciprocityTheory.ChartRestriction.G.FD.OrthonormalFlagTranslate (E := E) → ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartNormControl (E := E) → ReciprocityTheory.ChartRestriction.G.FD.NearSupremumTransference (E := E) → ReciprocityTheory.ChartRestriction.G.FD.SchwarzLemmaBall → ReciprocityTheory.ChartRestriction.G.FD.OrthonormalShortVectorBound (E := E) → ReciprocityTheory.ChartRestriction.G.FD.IsotropicCoefficientSplitting (E := E) → ReciprocityTheory.ChartRestriction.G.FD.NoShortVectorLowerBound (E := E) → ReciprocityTheory.ChartRestriction.G.FD.UnitaryUnipotentMove (E := E) → ReciprocityTheory.ChartRestriction.G.FD.FundamentalDomainPointBound (E := E) :=
  fun _ h0 h1 h2 h3 h4 _ _ h7 =>
    fundamentalDomain_of_parts fourierJacobi_differentiable fourierJacobi_boundaryEq fourierJacobi_bounded orthonormal_domain unitary_domain borel_flag_translate
      chartNorm_smul chartNorm_nonneg normFactor_pos_alt chart_zero_eq_alt h0 h1 h2 h3 h4 h7
