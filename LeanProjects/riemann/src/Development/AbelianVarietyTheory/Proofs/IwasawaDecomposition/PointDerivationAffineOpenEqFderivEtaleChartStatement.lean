import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointDerivationAffineOpenEqFderivEtaleChart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLatBasisZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanPeriodLatticeComplexSemiAbelianEqTopStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pointDerivation_affineOpen_eq_fderiv_etaleChart : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (n : ℕ) (σ : k →+* ℂ) (c : AlgChart p σ n) (x₀ : CxPts p σ), x₀ ∈ c.e.source → ∀ (U : Y.affineOpens), x₀ ∈ CxPts.ptsIn p σ U.1 → ∀ δ : Γ(Y, U.1) →+ ℂ, (∀ a : k, δ (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U.1 a) = 0) → (∀ g h : Γ(Y, U.1), δ (g * h) = CxPts.ev p σ U.1 g x₀ * δ h + CxPts.ev p σ U.1 h x₀ * δ g) → ∃ v : ReciprocityTheory.L2DbarEstimates.V n, ∀ g : Γ(Y, U.1), δ g = fderiv ℂ (CxPts.ev p σ U.1 g ∘ c.e.symm) (c.e x₀) v := by
  first | exact @GlobalTheory.PointDer.exists_eq_fderiv | exact GlobalTheory.PointDer.exists_eq_fderiv | (intros; apply GlobalTheory.PointDer.exists_eq_fderiv <;> assumption)
