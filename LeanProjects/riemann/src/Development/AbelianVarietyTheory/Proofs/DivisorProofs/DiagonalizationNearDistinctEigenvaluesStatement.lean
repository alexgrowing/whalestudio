import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalizationNearDistinctEigenvalues
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNonarchimedeanW
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag GlobalTheory.WholeFlag GlobalTheory.ConstLat
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_colMinor_mul_Iic_sub_Iio_eq_block_add_log : ∀ {K : Type} [Field K] (w : AbsoluteValue K ℝ), IsNonarchimedean w → ∀ {N g : ℕ} {ι : Type}
    (H : Matrix (Fin N) (Fin g) K) (P Q R : Matrix (Fin N) (Fin N) K) (b : Fin N → ι) (β : Fin g → ι) (χ : ι → K)
    (lam : ι → ℝ) (η ε : ℝ), 0 < η → η ≤ 1 → ε < η ^ 3 → P * Q = 1 → (∀ i j, w (P i j) ≤ η⁻¹ ∧ w (Q i j) ≤ η⁻¹) →
    P * R * Q = Matrix.diagonal (fun r => χ (b r)) → (∀ σ τ, σ ≠ τ → η ≤ w (χ σ - χ τ)) →
    (∀ (τ : ι) (y : Fin N → K), (∀ r, b r ≠ τ → y r = 0) → supN w y = lam τ * supN w (Q.mulVec y)) →
    (∀ u : Fin g → K, supN w (H.mulVec u) ≤ 1 →
      supN w (R.mulVec (H.mulVec u) - H.mulVec fun l => χ (β l) * u l) ≤ ε) →
    0 < colMinor w H Finset.univ →
    0 < colMinor w (P * H) Finset.univ ∧ ∀ i : Fin g, 0 < lam (β i) ∧
      Real.log (colMinor w (P * H) (Finset.Iic i)) - Real.log (colMinor w (P * H) (Finset.Iio i)) =
        Real.log (colMinor w H (blkLe β i)) - Real.log (colMinor w H (blkLt β i)) + Real.log (lam (β i)) := by
  first | exact @GlobalTheory.ConstLat.EigenMinor.graded_minor_log_eigen | exact GlobalTheory.ConstLat.EigenMinor.graded_minor_log_eigen | (intros; apply GlobalTheory.ConstLat.EigenMinor.graded_minor_log_eigen <;> assumption)
