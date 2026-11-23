import Mathlib
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.AdmissibleOfIwasawa
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.QuantumDeterminantEigenvalue
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.CasimirScalarOfCapelliDeterminantEigenvalueImpor
import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.IsSimpleFam
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker

noncomputable section

namespace GlobalTheory.CompanionTheory.CasimirDS

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

variable {k r : ℕ}

theorem qdet_smooth (hC : PI.DSInfCharCap.DSInfCharCap) (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool)
    (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r) (hR : R.IsDS ε mu) (Q : Mx k r)
    (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub) (hQ : IsUnit Q) (hE : R.IsE Q E)
    (Y : ℂ) (w : R.smSub) :
    Formalism.REAL.qdet E (Y + ((((2 * r + k + 1) : ℕ) : ℂ) - 1) / 2) w = (∏ s, (Y + (mu s : ℂ))) • w := by
  have hK : PI.KFinSmooth := CompanionTheory.D.gk.admitted.k_finite_smooth
  obtain ⟨hmu, Q0, hQ0, hDS⟩ := id hR
  have hU0 : IsUnit Q0 := hQ0.1.1
  obtain ⟨E0, hE0, hgl⟩ := GlobalTheory.T.smoothVectors_discreteSeries_glModule hK k r ε mu R hR Q0 hU0
  obtain ⟨hsm, hd⟩ := GlobalTheory.T.smoothVectors_complexDerivedAction_cayleyTransport k r ε R Q0 hQ0
  obtain ⟨-, hexp, -⟩ := GlobalTheory.T.derivedAction_expand_matrixUnits hK k r ε mu R hR Q0 E0 hU0 hE0
  have hdQ : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).1 hQ
  have hdQ0 : IsUnit Q0.det := (Matrix.isUnit_iff_isUnit_det Q0).1 hU0
  have hEE : E = Formalism.FourierDecayAlt.Q.Econj E0 (Q0 * Q⁻¹) (Q * Q0⁻¹) := by
    funext a b
    refine LinearMap.ext fun v => Subtype.ext ?_
    rw [hE a b v, hexp]
    have h1 : Q0 * (Q⁻¹ * Matrix.single a b (1 : ℂ) * Q) * Q0⁻¹ =
        (Q0 * Q⁻¹) * Matrix.single a b (1 : ℂ) * (Q * Q0⁻¹) := by
      simp only [Matrix.mul_assoc]
    rw [h1]
    simp only [GlobalTheory.CapelliSmooth.entry_conj, Formalism.FourierDecayAlt.Q.Econj, LinearMap.sum_apply, LinearMap.smul_apply,
      Submodule.coe_sum, Submodule.coe_smul]
  have h2 : (Q * Q0⁻¹) * (Q0 * Q⁻¹) = 1 := by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hdQ0, Matrix.mul_nonsing_inv _ hdQ]
  have h3 : (Q0 * Q⁻¹) * (Q * Q0⁻¹) = 1 := by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hdQ, Matrix.mul_nonsing_inv _ hdQ0]
  rw [hEE, covariant_det_of_lin covariant_linear _ _ E0 _ _ hgl h2 h3]
  apply Subtype.ext
  have h4 := GlobalTheory.T.freeAlgebraAction_capelliDeterminant_eq_operator _ ε R.H (fun g => R.σ (Q0⁻¹ * g * Q0)) R.smSub E0
    (fun a b v => by rw [hd, hE0 a b v]; rfl) (Y + ((((2 * r + k + 1) : ℕ) : ℂ) - 1) / 2) w
  rw [← h4, hC _ ε mu R.H _ hmu hDS w (hsm w w.2) Y]
  rfl

theorem dC_coe (U : URep k r) (Y : Mx k r) (v : U.R.smSub) : (U.dC Y v : U.R.H) = U.R.dC Y v := by
  have h1 := U.dsig_coe (X := reH k r Y) (GlobalTheory.ComplexifiedAction.lie_re Y) v
  have h2 := U.dsig_coe (X := imH k r Y) (GlobalTheory.ComplexifiedAction.lie_im Y) v
  simp only [URep.dC, LinearMap.add_apply, LinearMap.smul_apply, Submodule.coe_add, Submodule.coe_smul, h1, h2]
  rfl

theorem isE_one (U : URep k r) : U.R.IsE 1 (fun a b => U.dC (Matrix.single a b 1)) := by
  intro a b v
  rw [dC_coe, inv_one, Matrix.one_mul, Matrix.mul_one]

theorem cas_smooth (hC : PI.DSInfCharCap.DSInfCharCap) {ε : Fin (2 * r + k + 1) → Bool}
    {μ : Fin (2 * r + k + 1) → ℝ} (U : URep k r) (hk : 1 ≤ k) (hU : U.R.IsDS ε μ) (w : U.R.smSub) :
    (∑ a, ∑ b, U.dC (Matrix.single a b 1) * U.dC (Matrix.single b a 1)) w = (casG μ : ℂ) • w :=
  GlobalTheory.T.casimir_scalar_of_capelliDeterminant_eigenvalue U.R.smSub (2 * r + k + 1) (fun a b => U.dC (Matrix.single a b 1)) μ (by omega)
    (GlobalTheory.T.derivedAction_expand_matrixUnits CompanionTheory.D.gk.admitted.k_finite_smooth k r ε μ U.R hU 1 _ isUnit_one (isE_one U)).1
    (qdet_smooth hC k r ε μ U.R hU 1 _ isUnit_one (isE_one U)) w

theorem triv_dC (Y : Mx k r) : (triv k r).dC Y = 0 := by
  have h : ∀ X : Mx k r, (triv k r).dR X = 0 := by
    intro X
    funext c d
    simp [FRep.dR]
  simp [FRep.dC, h]

theorem L_one (U : URep k r) (Y : Mx k r) (x : M (one U)) (c : Unit) : L (one U) Y x c = U.dC Y (x c) := by
  have h : (one U).1.dC Y = 0 := triv_dC Y
  simp [L, h, dOp, mAct]

theorem casDS : CasDS := by
  intro hC k r ε μ U hk hU F
  constructor
  · refine LinearMap.ext fun x => funext fun c => ?_
    exact cas_smooth hC U hk hU (x c)
  · refine LinearMap.ext fun x => funext fun c => ?_
    have h := cas_smooth hC U hk hU (x c)
    simp only [LinearMap.sum_apply, Module.End.mul_apply] at h
    simp only [cas, LinearMap.sum_apply, Finset.sum_apply, Module.End.mul_apply, L_one]
    exact h

end GlobalTheory.CompanionTheory.CasimirDS

end
