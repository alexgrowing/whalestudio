import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SjIffJensenInequality

set_option autoImplicit false

noncomputable section

open MvPolynomial NumberField Module GlobalTheory.ChowHt GlobalTheory.CompHt MeasureTheory

namespace GlobalTheory.SphereMeanFrame

open GlobalTheory.IndefiniteRowSideFullHecke.UnitSphereMeasure

def sphereHomeo {N : ℕ} (e : EuclideanSpace ℂ (Fin (N + 1)) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin (N + 1))) :
    UnitSphere N ≃ₜ UnitSphere N where
  toFun := sphereMap e
  invFun := sphereMap e.symm
  left_inv z := Subtype.ext (e.symm_apply_apply z.1)
  right_inv z := Subtype.ext (e.apply_symm_apply z.1)
  continuous_toFun := Continuous.subtype_mk (e.continuous.comp continuous_subtype_val) _
  continuous_invFun := Continuous.subtype_mk (e.symm.continuous.comp continuous_subtype_val) _

set_option autoImplicit false in
open MvPolynomial NumberField Module MeasureTheory in

theorem _root_.GlobalTheory.SphereMeanFrame.eval_linSubst {B N n : ℕ} (M : Matrix (Fin N) (Fin n) ℂ)
    (f : MvPolynomial (Fin B × Fin N) ℂ) (u : Fin B × Fin n → ℂ) :
    eval u (_root_.GlobalTheory.ChowHt.linSubst M f) =
      eval (fun p : Fin B × Fin N => ∑ k, M p.2 k * u (p.1, k)) f := by
  unfold _root_.GlobalTheory.ChowHt.linSubst
  rw [_root_.ReciprocityTheory.MultiplicativeHeights.eval_aeval_alt]
  simp

set_option autoImplicit false in
open MvPolynomial NumberField Module MeasureTheory in

theorem _root_.GlobalTheory.SphereMeanFrame.blockSphereMean_linSubst {B N : ℕ} (Q : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    (hQ : ∀ x : EuclideanSpace ℂ (Fin (N + 1)), ‖Matrix.toEuclideanLin Q x‖ = ‖x‖)
    (f : MvPolynomial (Fin B × Fin (N + 1)) ℂ) :
    _root_.ReciprocityTheory.MultiplicativeHeights.blockSphereMean B (N + 1) (_root_.GlobalTheory.ChowHt.linSubst Q f) = _root_.ReciprocityTheory.MultiplicativeHeights.blockSphereMean B (N + 1) f := by
  let T : EuclideanSpace ℂ (Fin (N + 1)) →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin (N + 1)) :=
    { toLinearMap := Matrix.toEuclideanLin Q, norm_map' := hQ }
  let U := T.toLinearIsometryEquiv rfl
  let V : EuclideanSpace ℂ (Fin (N + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin (N + 1)) :=
    { toLinearEquiv := U.toLinearEquiv.restrictScalars ℝ, norm_map' := U.norm_map }
  set μ : Measure (Fin B → _root_.ReciprocityTheory.MultiplicativeHeights.UnitSphereC (N + 1)) := Measure.pi fun _ => _root_.ReciprocityTheory.MultiplicativeHeights.sphereProb (N + 1) with hμ
  set Φ : (Fin B → _root_.ReciprocityTheory.MultiplicativeHeights.UnitSphereC (N + 1)) → (Fin B → _root_.ReciprocityTheory.MultiplicativeHeights.UnitSphereC (N + 1)) :=
    fun z b => _root_.ReciprocityTheory.MultiplicativeHeights.sphereMap V (z b) with hΦdef
  have hΦ : MeasurePreserving Φ μ μ := measurePreserving_pi _ _ (fun _ => _root_.ReciprocityTheory.MultiplicativeHeights.measurePreserving_sphereMap V)
  set g : (Fin B → _root_.ReciprocityTheory.MultiplicativeHeights.UnitSphereC (N + 1)) → ℝ := fun z => Real.log ‖eval (_root_.ReciprocityTheory.MultiplicativeHeights.blockPoint z) f‖ with hg
  have hcont : Continuous (fun z : Fin B → _root_.ReciprocityTheory.MultiplicativeHeights.UnitSphereC (N + 1) => _root_.ReciprocityTheory.MultiplicativeHeights.blockPoint z) := by
    unfold _root_.ReciprocityTheory.MultiplicativeHeights.blockPoint
    exact continuous_pi fun p => (continuous_apply p.2).comp
      ((_root_.ReciprocityTheory.MultiplicativeHeights.continuous_spherePoint (N + 1)).comp (continuous_apply p.1))
  have hgm : Measurable g :=
    Real.measurable_log.comp (((MvPolynomial.continuous_eval f).comp hcont).norm.measurable)
  have hpt : ∀ z, eval (_root_.ReciprocityTheory.MultiplicativeHeights.blockPoint z) (_root_.GlobalTheory.ChowHt.linSubst Q f) = eval (_root_.ReciprocityTheory.MultiplicativeHeights.blockPoint (Φ z)) f := by
    intro z
    rw [_root_.GlobalTheory.SphereMeanFrame.eval_linSubst]
    congr 1
  change ∫ z, Real.log ‖eval (_root_.ReciprocityTheory.MultiplicativeHeights.blockPoint z) (_root_.GlobalTheory.ChowHt.linSubst Q f)‖ ∂μ = ∫ z, g z ∂μ
  simp_rw [hpt]
  change ∫ z, g (Φ z) ∂μ = ∫ z, g z ∂μ
  rw [← integral_map hΦ.measurable.aemeasurable hgm.aestronglyMeasurable, hΦ.map_eq]

set_option autoImplicit false in
open MvPolynomial NumberField Module MeasureTheory in

theorem _root_.GlobalTheory.SphereMeanFrame.blockSphereMean_eq_of_frameNorm_eq : ∀ (B N : ℕ) (A A' : Matrix (Fin N) (Fin N) ℂ),
    A.det ≠ 0 → A'.det ≠ 0 → (∀ z, _root_.GlobalTheory.ChowHt.frameNorm A z = _root_.GlobalTheory.ChowHt.frameNorm A' z) →
    ∀ f : MvPolynomial (Fin B × Fin N) ℂ,
      _root_.ReciprocityTheory.MultiplicativeHeights.blockSphereMean B N (_root_.GlobalTheory.ChowHt.linSubst A f) = _root_.ReciprocityTheory.MultiplicativeHeights.blockSphereMean B N (_root_.GlobalTheory.ChowHt.linSubst A' f) := by
  intro B N A A' hA hA' hn f
  cases N with
  | zero =>
    have hAA : A = A' := Subsingleton.elim _ _
    rw [hAA]
  | succ N =>
    have hAu : IsUnit A.det := isUnit_iff_ne_zero.mpr hA
    have hA'u : IsUnit A'.det := isUnit_iff_ne_zero.mpr hA'
    have hAQ : A * (A⁻¹ * A') = A' := by
      rw [← mul_assoc, Matrix.mul_nonsing_inv _ hAu, one_mul]
    have key : _root_.GlobalTheory.ChowHt.linSubst A' f =
        _root_.GlobalTheory.ChowHt.linSubst (A⁻¹ * A') (_root_.GlobalTheory.ChowHt.linSubst A f) := by
      rw [_root_.GlobalTheory.HeightUnique.linSubst_linSubst, hAQ]
    rw [key, _root_.GlobalTheory.SphereMeanFrame.blockSphereMean_linSubst (A⁻¹ * A')]
    intro x
    have h1 := hn (A'.mulVec x.ofLp)
    simp only [_root_.GlobalTheory.ChowHt.frameNorm, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hA'u,
      Matrix.one_mulVec] at h1
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    convert h1 using 4 with i
    rfl

end GlobalTheory.SphereMeanFrame
