import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalPeriodMapExists
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsL2OnDiagonalOfIsL2Metric

open CategoryTheory AlgebraicGeometry Set Matrix MeasureTheory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CxPts GlobalTheory.ArInt
open GlobalTheory.LB (toMod)
open GlobalTheory.LieVB (omega unitSec dUnit)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Fl Pt IsPeriodMap cov per stdLat transl IsFactor IsMetric)
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Real CategoryTheory.Obj
open GlobalTheory GlobalTheory.TorsionForm

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_period_map_exists : ∀ (S : Scheme.{0}) (P : PPAS S) (B : Set (V 1)) (y : V 1 → (Sp ℂ ⟶ S)) (v₀ : V 1),
    IsOpen B → v₀ ∈ B → IsHolTo B y → (∀ v ∈ B, Nonempty (P.RiemannData (y v))) →
    ∃ r : ℝ, 0 < r ∧ Metric.ball v₀ r ⊆ B ∧ ∃ (τ : V 1 → Matrix (Fin P.g) (Fin P.g) ℂ)
      (ex : Pt (V 1) P.g → (Sp ℂ ⟶ P.A.left)),
      IsPeriodMap (Metric.ball v₀ r) τ ∧ IsHolTo (cov (Metric.ball v₀ r) P.g) ex ∧
      ∀ v ∈ Metric.ball v₀ r,
        (∀ z, ex (v, z) ≫ P.A.hom = y v) ∧
        (∀ z w, ∀ x x' : Over.mk (y v) ⟶ P.A, x.left = ex (v, z) → x'.left = ex (v, w) →
          (x * x').left = ex (v, z + w)) ∧
        (∀ x : Over.mk (y v) ⟶ P.A, ∃ z, x.left = ex (v, z)) ∧
        (∀ z, ex (v, z) = y v ≫ unitSec P.A ↔ ∃ l ∈ stdLat P.g, z = per (τ v) l) ∧
        ∀ d : P.RiemannData (y v), ∃ F : (Fin P.g → ℂ) →ₗ[ℂ] (Fin P.g → ℂ),
          (∀ z, (d.u.ex (F z)).left ≫ d.φ = ex (v, z)) ∧
          ∀ z w, HermFrame.form d.H (F z) (F w) = GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.herm (τ v) z w := by
  first | exact @GlobalTheory.NormPeriods.exists_normalised_periods | exact GlobalTheory.NormPeriods.exists_normalised_periods | (intros; apply GlobalTheory.NormPeriods.exists_normalised_periods <;> assumption)
