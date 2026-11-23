import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultOfNotMem
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix
open scoped ComplexOrder

namespace GlobalTheory.PointChern

open GlobalTheory.HermFrame Matrix

section LinearModel

variable {n p q : ℕ} (Z : ReciprocityTheory.L2DbarEstimates.V n →ₗ[ℂ] Matrix (Fin p) (Fin q) ℂ)

noncomputable def linMatEntry (a : Fin p) (b : Fin q) : ReciprocityTheory.L2DbarEstimates.V n →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun u => Z u a b
      map_add' := fun u v => by simp
      map_smul' := fun c u => by simp }

theorem mContDiffAt_linMat (k : WithTop ℕ∞) (x : ReciprocityTheory.L2DbarEstimates.V n) :
    MContDiffAt k (fun u => Z u) x := fun a b => by
  have : (fun u => Z u a b) = ((linMatEntry Z a b).restrictScalars ℝ : ReciprocityTheory.L2DbarEstimates.V n →L[ℝ] ℂ) := by
    funext u; rfl
  rw [this]
  exact ContinuousLinearMap.contDiff _ |>.contDiffAt

theorem mdel_linMat (x ξ : ReciprocityTheory.L2DbarEstimates.V n) : mdel (fun u => Z u) x ξ = Z ξ := by
  ext a b
  have : (fun u => Z u a b) = fun u => linMatEntry Z a b u := rfl
  rw [mdel_apply, this, del_eq_fderiv (linMatEntry Z a b).differentiableAt,
    ContinuousLinearMap.fderiv]
  rfl

theorem mdbar_linMat (x η : ReciprocityTheory.L2DbarEstimates.V n) : mdbar (fun u => Z u) x η = 0 := by
  ext a b
  have : (fun u => Z u a b) = fun u => linMatEntry Z a b u := rfl
  rw [mdbar_apply, this, dbar_eq_zero (linMatEntry Z a b).differentiableAt]
  rfl

theorem mdel_linMat_conjTranspose (x ξ : ReciprocityTheory.L2DbarEstimates.V n) :
    mdel (fun u => (Z u)ᴴ) x ξ = 0 := by
  rw [mdel_conjTranspose, mdbar_linMat, conjTranspose_zero]

theorem mdbar_linMat_conjTranspose (x η : ReciprocityTheory.L2DbarEstimates.V n) :
    mdbar (fun u => (Z u)ᴴ) x η = (Z η)ᴴ := by
  rw [mdbar_conjTranspose, mdel_linMat]

theorem mdel_const_sub {m l : Type*} {B : ReciprocityTheory.L2DbarEstimates.V n → Matrix m l ℂ}
    {x : ReciprocityTheory.L2DbarEstimates.V n} (C : Matrix m l ℂ) (h : MContDiffAt 1 B x) (ξ : ReciprocityTheory.L2DbarEstimates.V n) :
    mdel (fun u => C - B u) x ξ = -mdel B x ξ := by
  ext a b
  simp only [mdel_apply, Matrix.sub_apply, Matrix.neg_apply]
  rw [del_sub (differentiableAt_const _) (h.diff a b)]
  simp

theorem mdbar_const_sub {m l : Type*} {B : ReciprocityTheory.L2DbarEstimates.V n → Matrix m l ℂ}
    {x : ReciprocityTheory.L2DbarEstimates.V n} (C : Matrix m l ℂ) (h : MContDiffAt 1 B x) (η : ReciprocityTheory.L2DbarEstimates.V n) :
    mdbar (fun u => C - B u) x η = -mdbar B x η := by
  ext a b
  simp only [mdbar_apply, Matrix.sub_apply, Matrix.neg_apply]
  rw [dbar_sub (differentiableAt_const _) (h.diff a b)]
  simp

theorem curv_modelGram_lie (w ξ η : ReciprocityTheory.L2DbarEstimates.V n) (hw : (1 - (Z w)ᴴ * Z w).PosDef) :
    curv (fun u => (1 - (Z u).map (starRingEnd ℂ) * (Z u)ᵀ)⁻¹) w ξ η =
      -(Z ξ * (1 - (Z w)ᴴ * Z w)⁻¹ * (Z η)ᴴ * (1 - Z w * (Z w)ᴴ)⁻¹) := by
  have hZ : ∀ x, MContDiffAt 2 (fun u => Z u) x := mContDiffAt_linMat Z 2
  have hB : ∀ x, MContDiffAt 2 (fun u => Z u * (Z u)ᴴ) x :=
    fun x => (hZ x).mul (hZ x).conjTranspose
  have hA : ∀ x, MContDiffAt 2 (fun u => 1 - Z u * (Z u)ᴴ) x :=
    fun x => (mContDiffAt_const 1).sub (hB x)
  have hAu : IsUnit (1 - Z w * (Z w)ᴴ).det := by
    rw [det_one_sub_mul_comm]; exact hw.det_pos.ne'.isUnit
  have hH : (fun u => (1 - (Z u).map (starRingEnd ℂ) * (Z u)ᵀ)⁻¹) =
      fun u => ((1 - Z u * (Z u)ᴴ)⁻¹)ᵀ := by
    funext u
    have e : 1 - (Z u).map (starRingEnd ℂ) * (Z u)ᵀ = (1 - Z u * (Z u)ᴴ)ᵀ := by
      ext a b
      simp [Matrix.mul_apply, Matrix.one_apply, Matrix.sub_apply, eq_comm, mul_comm]
    rw [e, transpose_nonsing_inv]
  have hconn : ∀ x, IsUnit (1 - Z x * (Z x)ᴴ).det →
      conn (fun u => ((1 - Z u * (Z u)ᴴ)⁻¹)ᵀ) x ξ = Z ξ * (Z x)ᴴ * (1 - Z x * (Z x)ᴴ)⁻¹ := by
    intro x hx
    have h1 : MContDiffAt 1 (fun u => 1 - Z u * (Z u)ᴴ) x := (hA x).of_le one_le_two
    have hZ1 : MContDiffAt 1 (fun u => Z u) x := (hZ x).of_le one_le_two
    have hdA : mdel (fun u => 1 - Z u * (Z u)ᴴ) x ξ = -(Z ξ * (Z x)ᴴ) := by
      rw [mdel_const_sub _ ((hB x).of_le one_le_two), mdel_mul hZ1 hZ1.conjTranspose,
        mdel_linMat, mdel_linMat_conjTranspose, Matrix.mul_zero, zero_add]
    rw [conn, transpose_transpose, nonsing_inv_nonsing_inv _ hx,
      mdel_transpose (fun u => (1 - Z u * (Z u)ᴴ)⁻¹), transpose_transpose, mdel_inv h1 hx, hdA]
    simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_assoc,
      mul_nonsing_inv_cancel_left _ _ hx]
  have hev : (fun x => conn (fun u => ((1 - Z u * (Z u)ᴴ)⁻¹)ᵀ) x ξ) =ᶠ[𝓝 w]
      fun x => Z ξ * (Z x)ᴴ * (1 - Z x * (Z x)ᴴ)⁻¹ :=
    ((hA w).eventually_isUnit hAu).mono fun x hx => hconn x hx
  have h1 : MContDiffAt 1 (fun u => 1 - Z u * (Z u)ᴴ) w := (hA w).of_le one_le_two
  have hZ1 : MContDiffAt 1 (fun u => Z u) w := (hZ w).of_le one_le_two
  have hdA : mdbar (fun u => 1 - Z u * (Z u)ᴴ) w η = -(Z w * (Z η)ᴴ) := by
    rw [mdbar_const_sub _ ((hB w).of_le one_le_two), mdbar_mul hZ1 hZ1.conjTranspose,
      mdbar_linMat, mdbar_linMat_conjTranspose, Matrix.zero_mul, add_zero]
  rw [hH, curv, mdbar_congr hev,
    mdbar_mul ((mContDiffAt_const (Z ξ)).mul hZ1.conjTranspose) (h1.inv hAu), mdbar_inv h1 hAu,
    mdbar_mul (mContDiffAt_const _) hZ1.conjTranspose, mdbar_linMat_conjTranspose, mdbar_const,
    hdA]
  have hP : (1 - Z w * (Z w)ᴴ) * (1 - Z w * (Z w)ᴴ)⁻¹ = 1 := mul_nonsing_inv _ hAu
  have hQ : (1 - (Z w)ᴴ * Z w)⁻¹ = 1 + (Z w)ᴴ * (1 - Z w * (Z w)ᴴ)⁻¹ * Z w := by
    apply Matrix.inv_eq_right_inv
    have e : (1 - (Z w)ᴴ * Z w) * (1 + (Z w)ᴴ * (1 - Z w * (Z w)ᴴ)⁻¹ * Z w) =
        1 - (Z w)ᴴ * Z w + (Z w)ᴴ * ((1 - Z w * (Z w)ᴴ) * (1 - Z w * (Z w)ᴴ)⁻¹) * Z w := by
      simp only [Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.one_mul,
        Matrix.mul_one, Matrix.mul_assoc]
    rw [e, hP, Matrix.mul_one, sub_add_cancel]
  rw [hQ]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_neg,
    Matrix.neg_mul, neg_neg, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_assoc, neg_add]
  abel

end LinearModel

end GlobalTheory.PointChern
