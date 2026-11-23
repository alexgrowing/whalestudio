import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.FormalDegreeConstantDiscrete
import CompanionTheory.AutomorphicTheory.SchurLimitBounds.ZuckermanDuality.ZuckDualTOfZuckDual

namespace CompanionTheory.Zuck

theorem zuckT_thrS : CompanionTheory.LimBd.Main.ZuckT fun _ ε => ReciprocityTheory.ChartRestriction.DS.G2.thrS ε := by
  intro n ε μ H _ _ _ σ hμ hσ h hg hlt
  obtain ⟨X, -⟩ := ReciprocityTheory.ChartRestriction.DS.G2.zuckerman_tensor_exists n ε μ H σ hμ hσ h hg hlt
  exact ⟨X⟩

theorem zuckDualT_thrS : CompanionTheory.LimBd.Main.ZuckDualT fun _ ε => ReciprocityTheory.ChartRestriction.DS.G2.thrS ε := by
  intro n ε μ H _ _ _ σ hμ hσ h hg hlt
  obtain ⟨X, -⟩ := ReciprocityTheory.ChartRestriction.DS.G2.zuckerman_dual_tensor_exists n ε μ H σ hμ hσ h hg hlt
  exact ⟨X⟩

end CompanionTheory.Zuck
