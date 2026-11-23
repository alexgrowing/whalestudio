import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsTateZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryInvariantHermitianFormSymmEqSmulTrace
open CategoryTheory AlgebraicGeometry Set Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.ArInt GlobalTheory.TorsionForm GlobalTheory.ThetaRR
open GlobalTheory.LB (toMod)
open GlobalTheory.LieVB (omega)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Fl Pt stdLat symMat tauU siegel symPart ChernIsFlat IsMetric InducesPolarisation cov)
open ReciprocityTheory.L2DbarEstimates (V)
open Filter Topology
open scoped ContDiff

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SiegelDens

variable {g : ℕ}

theorem im_congr (A X : Matrix (Fin g) (Fin g) ℝ) (τ : Matrix (Fin g) (Fin g) ℂ) :
    ((A.map (fun t : ℝ => (t : ℂ)) * τ * (A.map (fun t : ℝ => (t : ℂ)))ᵀ
        + X.map (fun t : ℝ => (t : ℂ))).map fun t => (t.im : ℂ))
      = A.map (fun t : ℝ => (t : ℂ)) * (τ.map fun t => (t.im : ℂ))
        * (A.map (fun t : ℝ => (t : ℂ)))ᵀ := by
  ext i j
  simp [Matrix.mul_apply, Complex.im_sum, Complex.re_sum, Finset.sum_mul]

theorem star_congr (A : Matrix (Fin g) (Fin g) ℝ) (Z : Matrix (Fin g) (Fin g) ℂ) :
    (A.map (fun t : ℝ => (t : ℂ)) * Z * (A.map (fun t : ℝ => (t : ℂ)))ᵀ).map star
      = A.map (fun t : ℝ => (t : ℂ)) * Z.map star * (A.map (fun t : ℝ => (t : ℂ)))ᵀ := by
  ext i j
  simp [Matrix.mul_apply, Finset.sum_mul]

theorem trace_congr (B Y Z W : Matrix (Fin g) (Fin g) ℂ) (hB : IsUnit B.det) :
    ((B * Y * Bᵀ)⁻¹ * (B * Z * Bᵀ) * (B * Y * Bᵀ)⁻¹ * (B * W * Bᵀ)).trace
      = (Y⁻¹ * Z * Y⁻¹ * W).trace := by
  have hT : IsUnit Bᵀ.det := by rwa [Matrix.det_transpose]
  have e : (B * Y * Bᵀ)⁻¹ * (B * Z * Bᵀ) * (B * Y * Bᵀ)⁻¹ * (B * W * Bᵀ)
      = Bᵀ⁻¹ * ((Y⁻¹ * Z * Y⁻¹ * W) * Bᵀ) := by
    simp only [Matrix.mul_inv_rev, Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hB,
      Matrix.mul_nonsing_inv_cancel_left _ _ hT]
  rw [e, Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hT, Matrix.mul_one]

theorem sdens_congr : ∀ (g : ℕ) (A X : Matrix (Fin g) (Fin g) ℝ) (τ Z : Matrix (Fin g) (Fin g) ℂ), IsUnit A → sdens (A.map (fun t : ℝ => (t : ℂ)) * τ * (A.map (fun t : ℝ => (t : ℂ)))ᵀ + X.map (fun t : ℝ => (t : ℂ))) (A.map (fun t : ℝ => (t : ℂ)) * Z * (A.map (fun t : ℝ => (t : ℂ)))ᵀ) = sdens τ Z := by
  intro g A X τ Z hA
  have hB : IsUnit (A.map (fun t : ℝ => (t : ℂ))).det := by
    have h := (Matrix.isUnit_iff_isUnit_det A).1 hA
    have e : (A.map (fun t : ℝ => (t : ℂ))).det = ((A.det : ℝ) : ℂ) :=
      (Complex.ofRealHom.map_det A).symm
    rw [e, isUnit_iff_ne_zero, Complex.ofReal_ne_zero]
    exact h.ne_zero
  unfold sdens
  rw [im_congr, star_congr, trace_congr _ _ _ _ hB]

end GlobalTheory.SiegelDens
