import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrthogonalSumPullbackIsometric
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orthogonal_sum_pullback_isometric : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (E₁ E₂ : X.Modules) (r s : ℕ) (h₁ : VMetric p E₁ r) (h₂ : VMetric p E₂ s) (π : Y ⟶ X) (hπ : π ≫ p = q), ∃ φ : ((Scheme.Modules.pullback π).obj E₁ ⊞ (Scheme.Modules.pullback π).obj E₂) ≅ (Scheme.Modules.pullback π).obj (E₁ ⊞ E₂), ((h₁.pull π hπ).orthSum (h₂.pull π hπ)).IsIsometry ((h₁.orthSum h₂).pull π hπ) φ := by
  first | exact @GlobalTheory.VMetric.isIsometry_pull_orthSum | exact GlobalTheory.VMetric.isIsometry_pull_orthSum | (intros; apply GlobalTheory.VMetric.isIsometry_pull_orthSum <;> assumption)
