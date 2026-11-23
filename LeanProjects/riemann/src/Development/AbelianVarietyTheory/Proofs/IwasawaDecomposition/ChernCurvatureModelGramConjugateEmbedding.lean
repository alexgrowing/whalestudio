import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultOfNotMem
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.PointChern

open GlobalTheory.HermFrame Matrix

section ModelCurv

variable {n p q : ℕ} (Z : ReciprocityTheory.L2DbarEstimates.V n →ₗ[ℂ] Matrix (Fin p) (Fin q) ℂ)

def entryCLM (a : Fin p) (b : Fin q) : ReciprocityTheory.L2DbarEstimates.V n →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap ((Matrix.entryLinearMap ℂ ℂ a b) ∘ₗ Z)

theorem mContDiffAt_linear {k : WithTop ℕ∞} (x : ReciprocityTheory.L2DbarEstimates.V n) :
    MContDiffAt k (fun u => Z u) x := fun a b => by
  have : (fun u => Z u a b) = ⇑(entryCLM Z a b) := rfl
  rw [this]
  exact ((entryCLM Z a b).contDiff.restrict_scalars ℝ).contDiffAt

theorem mdel_linear (x ξ : ReciprocityTheory.L2DbarEstimates.V n) : mdel (fun u => Z u) x ξ = Z ξ := by
  ext a b
  rw [mdel_apply]
  have : (fun u => Z u a b) = ⇑(entryCLM Z a b) := rfl
  rw [this, del_eq_fderiv (entryCLM Z a b).differentiableAt, (entryCLM Z a b).fderiv]
  rfl

theorem mdbar_linear (x η : ReciprocityTheory.L2DbarEstimates.V n) : mdbar (fun u => Z u) x η = 0 := by
  ext a b
  rw [mdbar_apply]
  have : (fun u => Z u a b) = ⇑(entryCLM Z a b) := rfl
  rw [this, dbar_eq_zero (entryCLM Z a b).differentiableAt]
  rfl

theorem mdel_one_sub_gram (x ξ : ReciprocityTheory.L2DbarEstimates.V n) :
    mdel (fun u => 1 - (Z u)ᴴ * Z u) x ξ = -((Z x)ᴴ * Z ξ) := by
  have h1 : MContDiffAt 1 (fun u => Z u) x := mContDiffAt_linear Z x
  have h := mdel_mul (A := fun u => (Z u)ᴴ) h1.conjTranspose h1 ξ
  rw [mdel_linear, mdel_conjTranspose, mdbar_linear, conjTranspose_zero, Matrix.zero_mul,
    add_zero] at h
  have e : (fun u => 1 - (Z u)ᴴ * Z u) = fun u => (fun _ => (1 : Matrix (Fin q) (Fin q) ℂ)) u
      + (fun u => -((Z u)ᴴ * Z u)) u := by funext u; simp [sub_eq_add_neg]
  rw [e, mdel_add (mContDiffAt_const _) (h1.conjTranspose.mul h1).neg, mdel_const, zero_add,
    mdel_neg, h]

theorem mdbar_one_sub_gram (x η : ReciprocityTheory.L2DbarEstimates.V n) :
    mdbar (fun u => 1 - (Z u)ᴴ * Z u) x η = -((Z η)ᴴ * Z x) := by
  have h1 : MContDiffAt 1 (fun u => Z u) x := mContDiffAt_linear Z x
  have h := mdbar_mul (A := fun u => (Z u)ᴴ) h1.conjTranspose h1 η
  rw [mdbar_linear, mdbar_conjTranspose, mdel_linear, Matrix.mul_zero, zero_add] at h
  have e : (fun u => 1 - (Z u)ᴴ * Z u) = fun u => (fun _ => (1 : Matrix (Fin q) (Fin q) ℂ)) u
      + (fun u => -((Z u)ᴴ * Z u)) u := by funext u; simp [sub_eq_add_neg]
  rw [e, mdbar_add (mContDiffAt_const _) (h1.conjTranspose.mul h1).neg, mdbar_const, zero_add,
    mdbar_neg, h]

theorem inv_one_sub_mul_conjTranspose (z : Matrix (Fin p) (Fin q) ℂ) (hu : IsUnit (1 - zᴴ * z).det) :
    (1 - z * zᴴ)⁻¹ = 1 + z * (1 - zᴴ * z)⁻¹ * zᴴ := by
  apply Matrix.inv_eq_right_inv
  have hAQ : (1 - zᴴ * z) * (1 - zᴴ * z)⁻¹ = 1 := mul_nonsing_inv _ hu
  set Q := (1 - zᴴ * z)⁻¹
  have hQ : Q = 1 + zᴴ * (z * Q) := by
    rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_iff_eq_add] at hAQ
    rw [Matrix.mul_assoc] at hAQ
    exact hAQ
  have key : z * (Q * zᴴ) = z * zᴴ + z * (zᴴ * (z * (Q * zᴴ))) := by
    nth_rewrite 1 [hQ]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_assoc]
  simp only [Matrix.sub_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]
  nth_rewrite 1 [key]
  abel

theorem curv_inv_one_sub_gram (w ξ η : ReciprocityTheory.L2DbarEstimates.V n) (hw : (1 - (Z w)ᴴ * Z w).PosDef) :
    curv (fun u => (1 - (Z u)ᴴ * Z u)⁻¹) w ξ η =
      -((1 - (Z w)ᴴ * Z w)⁻¹ * (Z η)ᴴ * (1 - Z w * (Z w)ᴴ)⁻¹ * Z ξ)ᵀ := by
  have hA : ∀ x, MContDiffAt 2 (fun u => 1 - (Z u)ᴴ * Z u) x := fun x =>
    (mContDiffAt_const 1).sub ((mContDiffAt_linear Z x).conjTranspose.mul (mContDiffAt_linear Z x))
  have hu : IsUnit (1 - (Z w)ᴴ * Z w).det := hw.det_pos.ne'.isUnit
  have hconn : ∀ x, IsUnit (1 - (Z x)ᴴ * Z x).det →
      conn (fun u => (1 - (Z u)ᴴ * Z u)⁻¹) x ξ = ((1 - (Z x)ᴴ * Z x)⁻¹ * (Z x)ᴴ * Z ξ)ᵀ := by
    intro x hx
    have h : (((1 - (Z x)ᴴ * Z x)⁻¹ * (Z x)ᴴ * Z ξ)ᵀ)ᵀ * (1 - (Z x)ᴴ * Z x)⁻¹ =
        mdel (fun u => (1 - (Z u)ᴴ * Z u)⁻¹) x ξ := by
      rw [transpose_transpose, mdel_inv ((hA x).of_le one_le_two) hx, mdel_one_sub_gram]
      simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]
    exact (eq_conn_of_compatible (H := fun u => (1 - (Z u)ᴴ * Z u)⁻¹) (z := x)
      (isUnit_nonsing_inv_det _ hx) h).symm
  have he : (fun x => conn (fun u => (1 - (Z u)ᴴ * Z u)⁻¹) x ξ) =ᶠ[𝓝 w]
      fun x => ((1 - (Z x)ᴴ * Z x)⁻¹ * (Z x)ᴴ * Z ξ)ᵀ :=
    ((hA w).eventually_isUnit hu).mono fun x hx => hconn x hx
  have hI : MContDiffAt 1 (fun x => (1 - (Z x)ᴴ * Z x)⁻¹) w := ((hA w).of_le one_le_two).inv hu
  have h1 : MContDiffAt 1 (fun u => Z u) w := mContDiffAt_linear Z w
  rw [curv, mdbar_congr he, mdbar_transpose (fun x => (1 - (Z x)ᴴ * Z x)⁻¹ * (Z x)ᴴ * Z ξ),
    mdbar_mul (A := fun x => (1 - (Z x)ᴴ * Z x)⁻¹ * (Z x)ᴴ) (B := fun _ => Z ξ)
      (hI.mul h1.conjTranspose) (mContDiffAt_const (Z ξ)), mdbar_const, Matrix.mul_zero, zero_add,
    mdbar_mul (A := fun x => (1 - (Z x)ᴴ * Z x)⁻¹) (B := fun x => (Z x)ᴴ) hI h1.conjTranspose,
    mdbar_inv ((hA w).of_le one_le_two) hu, mdbar_one_sub_gram, mdbar_conjTranspose, mdel_linear,
    inv_one_sub_mul_conjTranspose (Z w) hu]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.neg_mul, Matrix.mul_neg,
    neg_neg, Matrix.mul_assoc]

end ModelCurv

theorem curv_modelGram_tauBar : ∀ {n p q : ℕ} (Z : ReciprocityTheory.L2DbarEstimates.V n →ₗ[ℂ] Matrix (Fin p) (Fin q) ℂ)
    (w ξ η : ReciprocityTheory.L2DbarEstimates.V n), (1 - (Z w)ᴴ * Z w).PosDef →
    curv (fun u => (1 - (Z u)ᴴ * Z u)⁻¹) w ξ η =
      -((1 - (Z w)ᴴ * Z w)⁻¹ * (Z η)ᴴ * (1 - Z w * (Z w)ᴴ)⁻¹ * Z ξ)ᵀ :=
  fun Z w ξ η hw => curv_inv_one_sub_gram Z w ξ η hw

end GlobalTheory.PointChern
