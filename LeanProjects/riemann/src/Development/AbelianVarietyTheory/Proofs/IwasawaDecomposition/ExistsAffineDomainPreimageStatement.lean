import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineDomainPreimage
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsChartOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationBaseChangeModels
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.Reg GlobalTheory.FlagMod

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affine_domain_preimage : ∀ {X X' : Scheme.{0}} (v : X' ⟶ X), IsOpenImmersion v → ∀ (U : X.Opens), IsAffineOpen U → IsDomain Γ(X, U) → ∀ y : X', v y ∈ U → ∃ U' : X'.Opens, IsAffineOpen U' ∧ IsDomain Γ(X', U') ∧ y ∈ U' ∧ U' ≤ v ⁻¹ᵁ U := by
  first | exact @GlobalTheory.exists_affine_domain_open_preimage | exact GlobalTheory.exists_affine_domain_open_preimage | (intros; apply GlobalTheory.exists_affine_domain_open_preimage <;> assumption)
