import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
import GroundTheory.HeightsAndTheta.Heights.KernelsMatrix
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.AssemblyAnalytic
import GroundTheory.HeightsAndTheta.Heights.FactorialBounds.Assembly
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HasSumPolyDerivMulProdAddMatrix
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFundamentalDomainMeanNormSqThetaChar
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsUnitOfLagrangian
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.CoordSiegel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Nform

theorem re_dot_sub_re_hermForm {g : ℕ} (B : Matrix (Fin g) (Fin g) ℝ) (ζ : Fin g → ℂ) :
    (ζ ⬝ᵥ (B.map fun x : ℝ => (x : ℂ)).mulVec ζ).re - (hermForm (B.map fun x : ℝ => (x : ℂ)) ζ ζ).re =
      -2 * ((fun i => (ζ i).im) ⬝ᵥ B.mulVec fun i => (ζ i).im) := by
  simp only [hermForm, dotProduct, Matrix.mulVec, Matrix.map_apply, Pi.star_apply, Finset.mul_sum,
    Complex.re_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp
  ring

theorem periodMatrix_map_im {g : ℕ} (X Y : Matrix (Fin g) (Fin g) ℝ) :
    (GroundTheory.Heights₂.Heights.periodMatrix X Y).map Complex.im = Y := by
  ext i j
  simp [GroundTheory.Heights₂.Heights.periodMatrix]

theorem im_period_point {g : ℕ} (X Y : Matrix (Fin g) (Fin g) ℝ) (u₁ u₂ : Fin g → ℝ) :
    (fun i => (((GroundTheory.Heights₂.Heights.periodMatrix X Y).mulVec (fun i => (u₁ i : ℂ)) +
      (fun i => (u₂ i : ℂ))) i).im) = Y.mulVec u₁ := by
  funext i
  simp [GroundTheory.Heights₂.Heights.periodMatrix, Matrix.mulVec, dotProduct, Complex.im_sum]

theorem thetaChar_eq {g : ℕ} (X Y : Matrix (Fin g) (Fin g) ℝ) (a c : Fin g → ℝ) (ζ : Fin g → ℂ) :
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.thetaChar (GroundTheory.Heights₂.Heights.periodMatrix X Y)
        (fun i => (a i : ℂ)) (fun i => (c i : ℂ)) ζ =
      GroundTheory.Heights₂.Heights.thetaChar X Y a c ζ := by
  unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.thetaChar GroundTheory.Heights₂.Heights.thetaChar
  refine tsum_congr fun k => ?_
  have e : ((fun i => (k i : ℂ)) + fun i => (a i : ℂ)) =
      fun i => ((intVec k i + a i : ℝ) : ℂ) := by
    funext i
    simp [intVec]
  rw [e]

theorem norm_mul_canTh : ∀ (g : ℕ) (X Y : Matrix (Fin g) (Fin g) ℝ) (a c : Fin g → ℝ) (h Hm : Matrix (Fin g) (Fin g) ℂ)
    (θ : (Fin g → ℂ) → ℂ) (κ : ℂ),
    X.IsSymm → Y.PosDef →
    (∀ z w, hermForm Hm z w = hermForm (GlobalTheory.CanTh.imInv (periodMatrix X Y)) (h.mulVec z) (h.mulVec w)) →
    (∀ z, θ z = κ * GlobalTheory.CanTh.canTh (periodMatrix X Y) a c (h.mulVec z)) →
    ∀ (u₁ u₂ : Fin g → ℝ) (z : Fin g → ℂ),
      h.mulVec z = (periodMatrix X Y).mulVec (fun i => (u₁ i : ℂ)) + (fun i => (u₂ i : ℂ)) →
      ‖θ z‖ * Real.exp (-(Real.pi * ((1 : ℕ) : ℝ) / 2) * (hermForm Hm z z).re) = ‖κ‖ * thetaNorm X Y a c u₁ u₂ := by
  intro g X Y a c h Hm θ κ _ hY hH hθ u₁ u₂ z hz
  have him := periodMatrix_map_im X Y
  have hinv : GlobalTheory.CanTh.imInv (GroundTheory.Heights₂.Heights.periodMatrix X Y) =
      Y⁻¹.map fun x : ℝ => (x : ℂ) := by
    rw [GlobalTheory.CanTh.imInv, him]
  have hq : (fun i => ((h.mulVec z) i).im) = Y.mulVec u₁ := by
    rw [hz]
    exact im_period_point X Y u₁ u₂
  have hdiff := re_dot_sub_re_hermForm Y⁻¹ (h.mulVec z)
  have hcancel : Y⁻¹.mulVec (Y.mulVec u₁) = u₁ := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hY.det_pos.ne'.isUnit, Matrix.one_mulVec]
  rw [hq, hcancel, dotProduct_comm (Y.mulVec u₁) u₁, ← hinv] at hdiff
  have hqf : u₁ ⬝ᵥ Y.mulVec u₁ = qf Y u₁ := rfl
  rw [hqf] at hdiff
  rw [hθ z, hH z z, norm_mul, GlobalTheory.CanTh.canTh, norm_mul, Complex.norm_exp, thetaChar_eq, thetaNorm,
    ← hz]
  have hre : ((Real.pi / 2 : ℂ) * (h.mulVec z ⬝ᵥ
      (GlobalTheory.CanTh.imInv (GroundTheory.Heights₂.Heights.periodMatrix X Y)).mulVec (h.mulVec z))).re =
      Real.pi / 2 * (h.mulVec z ⬝ᵥ
      (GlobalTheory.CanTh.imInv (GroundTheory.Heights₂.Heights.periodMatrix X Y)).mulVec (h.mulVec z)).re := by
    have : ((Real.pi / 2 : ℂ)) = ((Real.pi / 2 : ℝ) : ℂ) := by push_cast; rfl
    rw [this, Complex.re_ofReal_mul]
  rw [hre]
  have hexp : Real.exp (Real.pi / 2 * (h.mulVec z ⬝ᵥ
      (GlobalTheory.CanTh.imInv (GroundTheory.Heights₂.Heights.periodMatrix X Y)).mulVec (h.mulVec z)).re) *
      Real.exp (-(Real.pi * ((1 : ℕ) : ℝ) / 2) *
        (hermForm (GlobalTheory.CanTh.imInv (GroundTheory.Heights₂.Heights.periodMatrix X Y))
          (h.mulVec z) (h.mulVec z)).re) = Real.exp (-Real.pi * qf Y u₁) := by
    rw [← Real.exp_add]
    congr 1
    push_cast
    linear_combination (Real.pi / 2) * hdiff
  calc _ = ‖κ‖ * (‖GroundTheory.Heights₂.Heights.thetaChar X Y a c (h.mulVec z)‖ *
        (Real.exp (Real.pi / 2 * (h.mulVec z ⬝ᵥ
          (GlobalTheory.CanTh.imInv (GroundTheory.Heights₂.Heights.periodMatrix X Y)).mulVec (h.mulVec z)).re) *
        Real.exp (-(Real.pi * ((1 : ℕ) : ℝ) / 2) *
          (hermForm (GlobalTheory.CanTh.imInv (GroundTheory.Heights₂.Heights.periodMatrix X Y))
            (h.mulVec z) (h.mulVec z)).re))) := by ring
    _ = _ := by rw [hexp]

end GlobalTheory.CompanionTheory.Ar.Nform
