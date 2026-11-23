import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussPropertyCodimOneChartHeightOnePrime
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussProperty_codimOne_chart_heightOnePrime : ∀ (σ : Setup) (x : Sp σ.R) (z : (σ.C x).G.left), Vert (σ.C x).G.hom (σ.ρ x σ.f) z → GaussAt (GlobalTheory.Desc.cst (σ.C x).G.hom) ((σ.C x).G.hom z).asIdeal (σ.θ x) (σ.W (spMap (σ.ρ x) ((σ.C x).G.hom z))) (regSet z) ∧ (σ.θ x) ⁻¹' (regSet z) = σ.W (spMap (σ.ρ x) ((σ.C x).G.hom z)) := by
  first | exact @GlobalTheory.Desc.GaussPt.gaussAt_vert | exact GlobalTheory.Desc.GaussPt.gaussAt_vert | (intros; apply GlobalTheory.Desc.GaussPt.gaussAt_vert <;> assumption)
