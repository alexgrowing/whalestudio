import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducesPl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTatePointDualBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentTraceSeparatingElementStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PAdicPointLinearFunctionalCmStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PAdicPointTraceDualStatement

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.EigenSplit GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.DetHT
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open Classical

noncomputable section

namespace GlobalTheory.EigDiff

theorem eigSt_holds : EigSt := by
  intro E _ _ _ _ H p _
  have hv : (Valued.v : Valuation ℂ_[p] ℝ≥0).Integers 𝓞_ℂ_[p] := Valuation.valuationSubring.integers _
  obtain ⟨δ, hδ0, hδ⟩ := GlobalTheory.T.idempotent_trace_separating_element E ℂ_[p] Valued.v 𝓞_ℂ_[p] hv
  refine ⟨δ, hδ0, ?_⟩
  intro l c _ _ Q τ w hw
  rw [htLat_psi]
  obtain ⟨⟨n, r, a, hsum⟩, hb⟩ := hδ (embAt c ℂ_[p] τ.1)
  constructor
  · intro h
    exact GlobalTheory.HTLat.Point.smul_latTQuot_le_latT Q _ δ r a hsum h
  · intro h
    obtain ⟨m, u, ℓ, e, h1, h2, h3⟩ := GlobalTheory.T.p_adic_point_linear_functional_cm Q (embAt c ℂ_[p] τ.1)
    exact GlobalTheory.T.p_adic_point_trace_dual Q _ δ hδ0 hb m u ℓ e h1 h2 h3 w hw h

end GlobalTheory.EigDiff
