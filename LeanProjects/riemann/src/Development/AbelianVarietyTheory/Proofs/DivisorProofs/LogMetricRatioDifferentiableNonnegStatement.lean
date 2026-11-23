import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogMetricRatioDifferentiableNonneg
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts
open CategoryTheory AlgebraicGeometry GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_metric_ratio_differentiable_nonneg : Hypotheses2 → HypothesesH → OnCore fun D O x P => ∀ (c : O.s.Comp) (σ : D.what₂.LL →+* ℂ) (ρ : DV.Rt D.what₂.Tau O.N)
  (y₀ : GlobalTheory.CxPts (O.var c).str σ), y₀ ∉ offBd O.Φ c σ →
  ∃ (ch : GlobalTheory.AlgChart (O.var c).str σ (O.var c).dim) (U : Set (GlobalTheory.CxPts (O.var c).str σ)) (C μ : ℝ),
    IsOpen U ∧ y₀ ∈ U ∧ U ⊆ ch.e.source ∧ 0 ≤ μ ∧ ∀ y ∈ U, y ∈ offBd O.Φ c σ →
      DifferentiableAt ℝ (lnRatio (metsOf x O.Φ c none σ (O.ex ρ)) (refMet x O.Φ c σ (O.ex ρ)) ∘ ch.e.symm) (ch.e y) ∧
      ∀ ξ : ReciprocityTheory.L2DbarEstimates.V (O.var c).dim,
        |fderiv ℝ (lnRatio (metsOf x O.Φ c none σ (O.ex ρ)) (refMet x O.Φ c σ (O.ex ρ)) ∘ ch.e.symm) (ch.e y) ξ| ≤
          C * O.met.r c σ y ^ μ * Real.exp (O.met.r c σ y / 2) * √(P.om c σ ch y ξ.ofLp) := by
  first | exact @GlobalTheory.HodgeGradNear.abs_fderiv_lnRatio_le_near | exact GlobalTheory.HodgeGradNear.abs_fderiv_lnRatio_le_near | (intros; apply GlobalTheory.HodgeGradNear.abs_fderiv_lnRatio_le_near <;> assumption)
