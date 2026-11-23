import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogBallBd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogBallBoundLocalChartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartPotentialRepresentationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KaehlerChartLogMeanBoundStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts
open AlgebraicGeometry MeasureTheory GlobalTheory.ChernReg GlobalTheory.ShFam GlobalTheory.CxPts Filter Topology

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogMean

theorem regLog_le_log_log : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.CovHt.HypothesesH → GlobalTheory.HeightParts.KernelSt → GlobalTheory.HeightParts.OnCore fun _ O _ P =>
    ∃ C t₀ : ℝ, 0 < C ∧ 0 < t₀ ∧ ∀ t : ℝ, 0 < t → t ≤ t₀ → ∀ (c : O.s.Comp) (σ : _ →+* ℂ)
      (ch : GlobalTheory.AlgChart (O.var c).str σ (O.var c).dim) (y : GlobalTheory.TrueGeo.Pts (O.var c) σ), y ∈ ch.e.source →
      Integrable (fun ξ => Real.log (O.met.r c σ (P.exph c σ ch y (t • ξ))) * GlobalTheory.ChernReg.cutoff (P.om c σ ch y ξ)) ∧
      rhoIn (P.om c σ) (P.exph c σ) (fun z => Real.log (O.met.r c σ z)) ch y t ≤ Real.log (C * Real.log (1 / t)) := by
  intro h2 hH hK D O x P hc hf hr
  have hcore : O.Core := ⟨x, P, hc⟩
  have key : ∀ (c : O.s.Comp) (σ : D.what₂.LL →+* ℂ), ∃ C t₀ : ℝ, 0 < C ∧ 0 < t₀ ∧ ∀ t : ℝ, 0 < t → t ≤ t₀ →
      ∀ (ch : GlobalTheory.AlgChart (O.var c).str σ (O.var c).dim) (y : GlobalTheory.TrueGeo.Pts (O.var c) σ), y ∈ ch.e.source →
      Integrable (fun ξ => Real.log (O.met.r c σ (P.exph c σ ch y (t • ξ))) * GlobalTheory.ChernReg.cutoff (P.om c σ ch y ξ)) ∧
      rhoIn (P.om c σ) (P.exph c σ) (fun z => Real.log (O.met.r c σ z)) ch y t ≤ Real.log (C * Real.log (1 / t)) := by
    intro c σ
    refine GlobalTheory.T.kaehler_chart_log_mean_bound hK (P.om c σ) (P.exph c σ) (O.met.r c σ) ((P.om_kaehler c σ).of_anRead _) (P.exph_is c σ)
      (fun y => hcore.exp_le_r c σ y) fun y₀ => ?_
    obtain ⟨ch, U, Φ, H, I, hy, hU, hyU, hUt, hΦ, hbij, hHc, he⟩ := GlobalTheory.T.chart_potential_representation h2 hH D O x P hc hf hr c σ y₀
    exact ⟨ch, hy, GlobalTheory.T.log_ball_bound_local_chart U (ch.e y₀) Φ H _ I hU hyU hΦ hbij hHc
      (fun v => (Real.exp_pos 1).le.trans (hcore.exp_le_r c σ _)) he⟩
  choose C t₀ hC ht₀ hb using key
  obtain ⟨M, hM⟩ := (Set.finite_range fun q : O.s.Comp × (D.what₂.LL →+* ℂ) => C q.1 q.2).bddAbove
  obtain ⟨N, hN⟩ := (Set.finite_range fun q : O.s.Comp × (D.what₂.LL →+* ℂ) => 1 / t₀ q.1 q.2).bddAbove
  refine ⟨max M 1, 1 / max N 2, by positivity, by positivity, fun t ht htt c σ ch y hy => ?_⟩
  have hN' : 1 / t₀ c σ ≤ max N 2 := (hN ⟨(c, σ), rfl⟩).trans (le_max_left _ _)
  have htc : t ≤ t₀ c σ := htt.trans ((one_div_le (ht₀ c σ) (by positivity)).1 hN')
  have ht1 : t < 1 := htt.trans_lt ((one_div_le_one_div_of_le two_pos (le_max_right N 2)).trans_lt (by norm_num))
  have hl : 0 < Real.log (1 / t) := Real.log_pos (one_lt_one_div ht ht1)
  obtain ⟨h1, h2'⟩ := hb c σ t ht htc ch y hy
  exact ⟨h1, h2'.trans (Real.log_le_log (mul_pos (hC c σ) hl)
    (mul_le_mul_of_nonneg_right ((hM ⟨(c, σ), rfl⟩).trans (le_max_left _ _)) hl.le))⟩

end GlobalTheory.LogMean
