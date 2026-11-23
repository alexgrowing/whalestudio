import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointPoly
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
import Formalism.DegreeFormula.Statement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeasurePreservingCompEquiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopChernDensityInvariantHolomorphicFrameChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniformisationComponentEqOfSameModulusPoint
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open MeasureTheory Formalism.DegreeFormula GlobalTheory.TrueCx
open scoped Matrix

namespace GlobalTheory.ModelMetricReg

open scoped ComplexOrder

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem contDiff_det {m : Type*} [Fintype m] [DecidableEq m] {k : WithTop ℕ∞}
    {F : E → Matrix m m ℂ} (hF : ∀ a b, ContDiff ℝ k (fun x => F x a b)) :
    ContDiff ℝ k (fun x => (F x).det) := by
  simp only [Matrix.det_apply']
  refine ContDiff.sum (fun σ _ => ?_)
  exact contDiff_const.mul (contDiff_prod (fun i _ => hF _ _))

theorem contDiff_adjugate_apply {m : Type*} [Fintype m] [DecidableEq m] {k : WithTop ℕ∞}
    {F : E → Matrix m m ℂ} (hF : ∀ a b, ContDiff ℝ k (fun x => F x a b)) (i j : m) :
    ContDiff ℝ k (fun x => (F x).adjugate i j) := by
  simp only [Matrix.adjugate_apply]
  refine contDiff_det (fun a b => ?_)
  by_cases hab : a = j
  · subst hab; simp only [Matrix.updateRow_self]; exact contDiff_const
  · simp only [Matrix.updateRow_ne hab]; exact hF a b

theorem det_one_sub_mul_conjTranspose_ne_zero {p q : ℕ} (z : Matrix (Fin p) (Fin q) ℂ)
    (hz : (1 - zᴴ * z).PosDef) : (1 - z * zᴴ).det ≠ 0 := by
  rw [Matrix.det_one_sub_mul_comm]
  exact hz.det_pos.ne'

end GlobalTheory.ModelMetricReg

namespace GlobalTheory.ModelMetricReg

open scoped ComplexOrder

theorem contDiff_hP_entry (ι : Type) [Fintype ι] (p q n : ℕ)
    (h : Fintype.card (ι × Fin p × Fin q) = n) (τ : ι) (a b : Fin p) :
    ContDiff ℝ 2 (fun w : ReciprocityTheory.L2DbarEstimates.V n => hP (unflat (GlobalTheory.UnifDens.flatL h w) τ) a b) := by
  have hz : ∀ c : ι × Fin p × Fin q,
      ContDiff ℝ 2 (fun w : ReciprocityTheory.L2DbarEstimates.V n => GlobalTheory.UnifDens.flatL h w c) := by
    intro c
    have hL : ContDiff ℝ 2 (fun w : ReciprocityTheory.L2DbarEstimates.V n => GlobalTheory.UnifDens.flatL h w) :=
      ((GlobalTheory.UnifDens.flatL h).contDiff).restrict_scalars ℝ
    exact (contDiff_apply ℝ ℂ c).comp hL
  simp only [hP, Matrix.sub_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, unflat,
    Matrix.of_apply]
  refine contDiff_const.sub (ContDiff.sum (fun k _ => ?_))
  have hs : ContDiff ℝ 2 (fun w : ReciprocityTheory.L2DbarEstimates.V n => star (GlobalTheory.UnifDens.flatL h w (τ, b, k))) := by
    have := (Complex.conjCLE.contDiff (n := 2)).comp (hz (τ, b, k))
    convert this using 2
    simp [Function.comp, Complex.conjCLE_apply, Complex.star_def]
  exact (hz (τ, a, k)).mul hs

theorem invT_contDiffAt_and_isUnit : ∀ (ι : Type) [Fintype ι] (p q n : ℕ) (h : Fintype.card (ι × Fin p × Fin q) = n) (v : ReciprocityTheory.L2DbarEstimates.V n), GlobalTheory.UnifDens.flatL h v ∈ DomFlat ι p q → ∀ τ : ι, MContDiffAt 2 (fun w => ((hP (unflat (GlobalTheory.UnifDens.flatL h w) τ))⁻¹)ᵀ) v ∧ IsUnit (((hP (unflat (GlobalTheory.UnifDens.flatL h v) τ))⁻¹)ᵀ).det := by
  intro ι _ p q n h v hv τ
  have hpos : (1 - (unflat (GlobalTheory.UnifDens.flatL h v) τ)ᴴ * unflat (GlobalTheory.UnifDens.flatL h v) τ).PosDef :=
    hv τ
  have hne : (hP (unflat (GlobalTheory.UnifDens.flatL h v) τ)).det ≠ 0 :=
    det_one_sub_mul_conjTranspose_ne_zero _ hpos
  refine ⟨fun a b => ?_, ?_⟩
  · have hE := contDiff_hP_entry ι p q n h τ
    have hdet := contDiff_det (F := fun w : ReciprocityTheory.L2DbarEstimates.V n => hP (unflat (GlobalTheory.UnifDens.flatL h w) τ)) hE
    have hadj := contDiff_adjugate_apply (F := fun w : ReciprocityTheory.L2DbarEstimates.V n => hP (unflat (GlobalTheory.UnifDens.flatL h w) τ)) hE b a
    simp only [Matrix.transpose_apply, Matrix.inv_def, Matrix.smul_apply, smul_eq_mul,
      Ring.inverse_eq_inv']
    exact (hdet.contDiffAt.inv hne).mul hadj.contDiffAt
  · rw [Matrix.det_transpose, Matrix.det_nonsing_inv]
    rw [Ring.inverse_eq_inv']
    exact (inv_ne_zero hne).isUnit

end GlobalTheory.ModelMetricReg
