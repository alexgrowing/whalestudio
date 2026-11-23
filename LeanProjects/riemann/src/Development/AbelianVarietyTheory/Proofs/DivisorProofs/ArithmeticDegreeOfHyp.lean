import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsCompModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopologicalKrullDimEqSucc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArithmeticVarietyCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInducedMetricApproximationStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.FlagPoly GlobalTheory.FlagAr
open CategoryTheory AlgebraicGeometry GlobalTheory GlobalTheory.TrueGeo GlobalTheory.ArInt ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.ProjVar

namespace GlobalTheory.Mean4O.TieArObj

theorem tieAr_onObj : Hypotheses2 → HypothesesH → OnObj fun _ _ A _ _ _ => TieAr A := by
  intro hP hH D O hC hf A T H h
  obtain ⟨s₀, hs₀, hap⟩ := GlobalTheory.T.exists_induced_metric_approximation hP hH D O hC hf A T H h
  refine ⟨s₀, hs₀, fun L c => Adl.SemiPos (L c), fun L c => Adl.NefFib (L c), fun L _ => ⟨Iff.rfl, Iff.rfl⟩,
    fun c => ?_⟩
  obtain ⟨M, -⟩ := GlobalTheory.IntModel.exists_model D.what₂.LL (O.var c) 0
  have hM : IsArithVar M.p (dimY O.Y) := by
    have := M.ar
    rw [O.dim_eq c] at this
    exact this
  obtain ⟨b, hb, hcm⟩ := GlobalTheory.Mean4O.CompModel.exists_isCompModel D O A h.aux c M hM
  refine ⟨@ArMod.mk _ (𝓞 D.what₂.LL) _ M.X hM.isIntegral M.p hM, b, hcm, fun L hL => ?_⟩
  have hI : ∃ (M' : TrueGeo.Model (O.var c)) (L' : HermLB M'.p) (k : ℕ+) (cf : HeightOneSpectrum (𝓞 D.what₂.LL) → ℝ),
      (L c).Induced M' L' k cf := by
    rcases hL with ⟨-, hn⟩ | hL
    · obtain ⟨M', L', k, cf, hI, -⟩ := hn c
      exact ⟨M', L', k, cf, hI⟩
    · exact hap L hL c
  obtain ⟨M', L', k, cf, hI⟩ := hI
  obtain ⟨X', i, q, π, hπ, H', n, d, hq, hs, hd, hd0, hn, h₁, h₂, h₃, h₄, h₅⟩ :=
    GlobalTheory.T.exists_arithmetic_variety_cover hP hH _ (O.var c) (dimY O.Y) (O.dim_eq c) (L c) M M' L' k cf hI
  refine ⟨X', i, q, π, hπ, H', n, d, hq, hs, hd, hd0, hn, h₁, h₂, h₃, h₄, fun y hy x hx e => ?_⟩
  subst hy
  rw [h.aux.ht L y]
  rw [hb y rfl] at e
  exact h₅ _ x hx e

end GlobalTheory.Mean4O.TieArObj
