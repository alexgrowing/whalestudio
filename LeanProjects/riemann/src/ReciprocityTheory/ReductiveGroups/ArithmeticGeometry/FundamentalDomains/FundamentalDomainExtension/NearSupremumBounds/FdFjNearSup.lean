import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainExtension.NearSupremumBounds.Inputs

theorem fd_fj_near_sup {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] : ReciprocityTheory.ChartRestriction.G.FD.HolomorphicPeriodicityExtension (E := E) → ReciprocityTheory.ChartRestriction.G.FD.FlowNormRatio (E := E) → ReciprocityTheory.ChartRestriction.G.FD.ModerateCoefficientPositivity (E := E) → ReciprocityTheory.ChartRestriction.G.FD.NearSupremumTransference (E := E) :=
  PI.FdFjNearSup.W.fd_fj_near_sup_full
