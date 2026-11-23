import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernPotentialPositiveOnComponentsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PositivePotentialMinusSmallMultiplePshStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalPotentialOfMetricExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PotentialChernFormSmoothFunctionExistsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

namespace GlobalTheory.CovHt

theorem qPolBd_onObj : Hypotheses2 → HypothesesH → OnObj fun _ _ A T _ _ => ∀ c, (T.F c).QPolBd A.dir := by
  intro hP hH D O hC _ A T H R c σ
  have pos := GlobalTheory.T.chern_potential_positive_on_components hP hH D O hC A T H R c σ
  obtain ⟨k, hk, hpsh⟩ := GlobalTheory.T.positive_potential_minus_small_multiple_psh ((T.M c).A σ) ((T.F c).a σ) ((T.M c).Om σ) (T.a_pot c σ) pos
    ((T.M c).bd σ).2.2.1
  obtain ⟨x, P, hxP⟩ := hC
  obtain ⟨m, L, s, hL, hLp, hs, n, mu, W, hsnc, hmu, hW⟩ := GlobalTheory.T.local_potential_of_metric_exists hP hH D O x P hxP A T H R c σ
  obtain ⟨g, hg, hlev⟩ := GlobalTheory.T.potential_chern_form_smooth_function_exists hP hH D O x P hxP A T H R c σ m L hL hLp
  refine ⟨fun y j z hz w => ?_, ⟨k, hk, hpsh⟩, L, s, g, hg, hLp, hs, ⟨n, mu, W, hsnc, hmu, hW⟩, hlev⟩
  by_cases hw : w = 0
  · subst hw; simp [ReciprocityTheory.AnForm.levi]
  · exact (pos y j z hz w hw).le

end GlobalTheory.CovHt
