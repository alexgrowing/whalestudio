import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ExistsPrincipalLattice
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Formalism.LocalToGlobal.ProjectiveLattices.L2DefiniteCuspForms
import Formalism.LocalToGlobal.ProjectiveLattices.NonnegIffOfLiesTotal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.NonvanishingNearMaximum
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsotropicCoefficientSplitting
import Formalism.LocalToGlobal.CMDeterminantIdeals.LambdaLowerBound
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.UnimodularAndTangentOfIsAH
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.KeyFormulaPowAndDegree
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.KeyUniq

theorem volume_image {g : ℕ} (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (s : Set (Fin g → ℂ)) :
    (volume (F '' s)).toReal = ‖LinearMap.det F‖ ^ 2 * (volume s).toReal := by
  have h := Measure.addHaar_image_linearMap volume (F.restrictScalars ℝ) s
  rw [LinearMap.det_restrictScalars, Algebra.norm_complex_apply, abs_of_nonneg (Complex.normSq_nonneg _),
    Complex.normSq_eq_norm_sq] at h
  rw [show (F '' s) = (F.restrictScalars ℝ) '' s from rfl, h, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]

theorem volume_fund {g : ℕ} (Λ Λ' : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ']
    (F : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (hF : ∀ z, F z ∈ Λ' ↔ z ∈ Λ) {s s' : Set (Fin g → ℂ)}
    (hs : IsAddFundamentalDomain Λ s volume) (hs' : IsAddFundamentalDomain Λ' s' volume) :
    (volume s').toReal = ‖LinearMap.det F.toLinearMap‖ ^ 2 * (volume s).toReal := by
  let φ : Λ' ≃ Λ :=
    { toFun := fun b => ⟨F.symm b, (hF _).1 (by rw [F.apply_symm_apply]; exact b.2)⟩
      invFun := fun a => ⟨F a, (hF a).2 a.2⟩
      left_inv := fun b => Subtype.ext (F.apply_symm_apply b.1)
      right_inv := fun a => Subtype.ext (F.symm_apply_apply a.1) }
  have hq : Measure.QuasiMeasurePreserving F.toEquiv.symm volume volume :=
    Measure.LinearMap.quasiMeasurePreserving volume (F.symm.restrictScalars ℝ).toLinearMap
      (F.symm.restrictScalars ℝ).isUnit_det'.ne_zero
  have h1 : IsAddFundamentalDomain Λ' (F.toEquiv '' s) volume :=
    hs.image_of_equiv F.toEquiv hq φ fun b z => by
      change F (F.symm b + z) = b + F z
      rw [map_add, F.apply_symm_apply]
  have : Countable Λ' := countable_of_Lindelof_of_discrete
  have : MeasurableConstVAdd Λ' (Fin g → ℂ) := ⟨fun c => measurable_const_add (c : Fin g → ℂ)⟩
  have : VAddInvariantMeasure Λ' (Fin g → ℂ) volume :=
    ⟨fun c s _ => measure_preimage_add volume (c : Fin g → ℂ) s⟩
  rw [hs'.measure_eq h1]
  exact volume_image F.toLinearMap s

theorem norm_eq_and_hermForm_eq : ∀ (x : KeyIn ℂ) (u : HolUnif x.P.A x.P.L x.P.g) (Hm : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (χ : u.Λ → ℂ) (θ : (Fin x.P.g → ℂ) → ℂ) (Fd : Set (Fin x.P.g → ℂ)) (u' : HolUnif x.P.A x.P.L x.P.g) (Hm' : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (χ' : u'.Λ → ℂ) (θ' : (Fin x.P.g → ℂ) → ℂ) (Fd' : Set (Fin x.P.g → ℂ)), u.IsAH Hm χ ∧ u.IsRig x.rig ∧ u.IsFn x.th θ ∧ IsAddFundamentalDomain u.Λ Fd volume → u'.IsAH Hm' χ' ∧ u'.IsRig x.rig ∧ u'.IsFn x.th θ' ∧ IsAddFundamentalDomain u'.Λ Fd' volume → (∫ z in Fd, ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm z z).re)) / (volume Fd).toReal = (∫ z in Fd', ‖θ' z‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm' z z).re)) / (volume Fd').toReal ∧ ∀ (v w : epsR ℂ ⟶ x.P.A) (V W V' W' : Fin x.P.g → ℂ), IsTangent v → IsTangent w → u.IsDiff V v → u.IsDiff W w → u'.IsDiff V' v → u'.IsDiff W' w → hermForm Hm V W = hermForm Hm' V' W' := by
  rintro x u Hm χ θ Fd u' Hm' χ' θ' Fd' ⟨hA, hR, hθ, hD⟩ ⟨hA', hR', hθ', hD'⟩
  obtain ⟨-, t1, -⟩ := unimodular_and_tangent_of_isAH thetaUnifAV_all x.P x.rig x.rig_gen u Hm χ hA
  obtain ⟨-, t1', t2'⟩ := unimodular_and_tangent_of_isAH thetaUnifAV_all x.P x.rig x.rig_gen u' Hm' χ' hA'
  obtain ⟨F, hF, -⟩ := GlobalTheory.existsUnique_linear_lift_of_isHolTo x.P.A x.P.isAb x.P.L x.P.g x.P.g u' t1' t2' u.ex u.ex_add
    (fun U f => by simpa only [Set.mem_univ, true_and] using u.hol U f)
  let e : (Fin x.P.g → ℂ) ≃ₗ[ℂ] (Fin x.P.g → ℂ) := LinearEquiv.ofInjectiveEndo F (UnifCompare.injective u u' F hF)
  have hd : ∀ w v, u.IsDiff w v ↔ u'.IsDiff (F w) v :=
    UnifCompare.isDiff_iff u u' e.toContinuousLinearEquiv hF
  refine ⟨?_, fun v w V W V' W' hv hw h1 h2 h3 h4 => ?_⟩
  · obtain ⟨N, hN, κ, -, -, -, -, hK⟩ := keyFormulaPow_and_keyDegree.1
    choose W hW using fun i => (t1 _ (x.basis.1 i)).exists
    have k := hK x u Hm (Matrix.of W) χ θ Fd _ _ hA hR hθ hW hD rfl rfl
    have k' := hK x u' Hm' (Matrix.of fun i => F (W i)) χ' θ' Fd' _ _ hA' hR' hθ' (fun i => (hd _ _).1 (hW i)) hD' rfl rfl
    have := u'.discrete
    have hvol : (volume Fd').toReal = ‖LinearMap.det F‖ ^ 2 * (volume Fd).toReal :=
      volume_fund u.Λ u'.Λ e (UnifCompare.mem_iff u u' F hF) hD hD'
    have hdet : (Matrix.of fun i => F (W i)).det = LinearMap.det F * (Matrix.of W).det := by
      have : (Matrix.of fun i => F (W i)) = Matrix.of W * (LinearMap.toMatrix' F).transpose := by
        ext i j
        rw [Matrix.of_apply, ← LinearMap.toMatrix'_mulVec, Matrix.mul_apply, Matrix.mulVec, dotProduct]
        exact Finset.sum_congr rfl fun _ _ => _root_.mul_comm _ _
      rw [this, Matrix.det_mul, Matrix.det_transpose, LinearMap.det_toMatrix', _root_.mul_comm]
    have h0 : ‖LinearMap.det F‖ ≠ 0 := norm_ne_zero_iff.2 e.isUnit_det'.ne_zero
    have hη : (volume Fd').toReal / (Real.pi ^ x.P.g * ‖(Matrix.of fun i => F (W i)).det‖ ^ 2) =
        (volume Fd).toReal / (Real.pi ^ x.P.g * ‖(Matrix.of W).det‖ ^ 2) := by
      rw [hvol, hdet, norm_mul, mul_pow, mul_left_comm, mul_div_mul_left _ _ (pow_ne_zero 2 h0)]
    rw [hη] at k'
    have hne := k.trans_ne (pow_ne_zero _ Real.two_pi_pos.ne')
    have h1 := mul_left_cancel₀ (left_ne_zero_of_mul (left_ne_zero_of_mul hne))
      (mul_right_cancel₀ (right_ne_zero_of_mul hne) (k.trans k'.symm))
    exact (pow_left_inj₀ (div_nonneg (integral_nonneg fun z => by positivity) ENNReal.toReal_nonneg)
      (div_nonneg (integral_nonneg fun z => by positivity) ENNReal.toReal_nonneg)
      (by have := hN x.P.g; omega)).1 h1
  · rw [(t1' v hv).unique h3 ((hd _ _).1 h1), (t1' w hw).unique h4 ((hd _ _).1 h2)]
    exact (UnifCompare.hermForm_eq x.P.isLB u u' hA hA' F hF V W).symm

end GlobalTheory.KeyUniq
