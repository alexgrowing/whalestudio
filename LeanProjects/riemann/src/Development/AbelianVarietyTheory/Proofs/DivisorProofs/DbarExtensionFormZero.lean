import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HermitianCurvatureForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovariantSecondFundamentalForm
import Development.AbelianVarietyTheory.Definitions.Divisors.DiagValExtTraceNonneg
open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HermitianCurvatureForms

noncomputable section
namespace GlobalTheory.DbarExt

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V]
  [IsScalarTower ℝ ℂ V]

theorem hasFDerivAt_fderiv_apply {f : V → ℂ} {z : V} (hf : ContDiffAt ℝ 2 f z) (u : V) :
    HasFDerivAt (fun x => fderiv ℝ f x u)
      ((ContinuousLinearMap.apply ℝ ℂ u).comp (fderiv ℝ (fderiv ℝ f) z)) z := by
  have hD : DifferentiableAt ℝ (fderiv ℝ f) z :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  exact (ContinuousLinearMap.apply ℝ ℂ u).hasFDerivAt.comp z hD.hasFDerivAt

theorem dbar_dbar_comm {f : V → ℂ} {z : V} (hf : ContDiffAt ℝ 2 f z) (v w : V) :
    dbar (fun x => dbar f x w) z v = dbar (fun x => dbar f x v) z w := by
  have hs : IsSymmSndFDerivAt ℝ f z := hf.isSymmSndFDerivAt (by simp)
  have key : ∀ u : V, HasFDerivAt (fun x => dbar f x u)
      ((1 / 2 : ℂ) • ((ContinuousLinearMap.apply ℝ ℂ u).comp (fderiv ℝ (fderiv ℝ f) z) +
        I • (ContinuousLinearMap.apply ℝ ℂ (I • u)).comp (fderiv ℝ (fderiv ℝ f) z))) z := by
    intro u
    have := ((hasFDerivAt_fderiv_apply hf u).add
      ((hasFDerivAt_fderiv_apply hf (I • u)).const_smul I)).const_smul (1 / 2 : ℂ)
    exact this
  rw [dbar_eq_of_hasFDerivAt (key w), dbar_eq_of_hasFDerivAt (key v)]
  simp only [antilinPart_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.apply_apply]
  rw [hs v w, hs v (I • w), hs (I • v) w, hs (I • v) (I • w)]
  ring_nf

theorem dbarAnti_extForm_eq_zero {m l : Type} [Fintype m] [Fintype l] [DecidableEq m]
    [DecidableEq l] {U : Set V} {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V} (h : IsHermFrame U H)
    (hs : ∀ x ∈ U, IsUnit (subGram (H x)).det) (hz : z ∈ U) (η₁ η₂ : V) :
    dbarAnti (extForm H) z η₁ η₂ = 0 := by
  have hc : ∀ a b, ContDiffAt ℝ 2 (fun x => orthCoeff (H x) a b) z := by
    intro a b
    have h1 := (GlobalTheory.IndefiniteRowSideFullHecke.CovariantSecondFundamentalForm.mContDiffAt_orthLift (h.mContDiffAt hz) (hs z hz)) (Sum.inl a) b
    have h2 : (fun x => orthCoeff (H x) a b) = fun x => -orthLift (H x) (Sum.inl a) b := by
      funext x; simp [orthLift]
    rw [h2]
    exact (h1.neg).of_le (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))
  simp only [dbarAnti, extForm_eq_neg_mdbar]
  ext a b
  simp only [Matrix.sub_apply, mdbar_apply, Matrix.neg_apply, Matrix.zero_apply, dbar_neg,
    ContinuousLinearMap.neg_apply]
  rw [dbar_dbar_comm (hc a b) η₁ η₂]
  simp

end GlobalTheory.DbarExt
