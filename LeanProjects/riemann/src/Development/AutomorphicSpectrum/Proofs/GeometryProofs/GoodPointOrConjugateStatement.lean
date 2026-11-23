import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GoodPointOrConjugate
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbBound
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.QuotUnif Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.good_point_or_conjugate : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (z : Sp ℂ ⟶ 𝔐.X), GoodPt 𝔐 z ∨ GoodPt 𝔐 (spMap (starRingEnd ℂ) ≫ z) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.QuotUnif.Dich.goodPt_or_conj | exact GlobalTheory.CompanionTheory.Ar.QuotUnif.Dich.goodPt_or_conj | (intros; apply GlobalTheory.CompanionTheory.Ar.QuotUnif.Dich.goodPt_or_conj <;> assumption)
