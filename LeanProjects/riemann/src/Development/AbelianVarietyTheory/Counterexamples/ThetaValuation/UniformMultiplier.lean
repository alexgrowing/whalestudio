import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.SupAtUnit
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.NegLogEpStar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ModelDataX
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ModelLattice
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.GamAtOfLawsCore
import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.LatticeAndConstantUnique

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
  ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatB
  ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLat

namespace GlobalTheory.ModelLatExamples

theorem eq_latP {r : ℕ} (D : D7) (Λ L : Submodule (𝓞 D.host.E) (Fin r → D.host.E))
    (h : Λ = Submodule.span (𝓞 D.host.E) {v | ∃ a ∈ D.host.AA, ∃ u ∈ L, v = a • u}) : L = lattice₂ D Λ := by
  have h2 := lat_eq_span Formalism.IndefR.Fin.factPrincipalDatum Λ
  apply le_antisymm
  · exact GlobalTheory.ModelLatticeCheck.le_of_span_le _ (GlobalTheory.ModelLatticeCheck.AA_ne_zero D) _ _ (by rw [← h, ← h2])
  · exact GlobalTheory.ModelLatticeCheck.le_of_span_le _ (GlobalTheory.ModelLatticeCheck.AA_ne_zero D) _ _ (by rw [← h, ← h2])

end GlobalTheory.ModelLatExamples
