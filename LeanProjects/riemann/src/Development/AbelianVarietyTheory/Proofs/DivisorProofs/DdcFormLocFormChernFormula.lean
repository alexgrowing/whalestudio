import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPosFrameQuotIn
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HermitianCurvatureForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubquotientCurvatureStatement

open Set Matrix Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.HermFrame GlobalTheory.CxForm GlobalTheory.SecForm
open GlobalTheory.GoodMetric (coordVec)
open scoped ContDiff ComplexOrder

noncomputable section

namespace GlobalTheory.SecForm.DdcLoc

section Calc

open Complex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E] {z : E}

theorem del_del_comm {u : E → ℂ} (hu : ContDiffAt ℝ 2 u z) (v w : E) :
    del (fun x => del u x v) z w = del (fun x => del u x w) z v := by
  have h := (differentiableAt_fderiv_of_contDiffAt_two hu)
  have h1 : ∀ a, DifferentiableAt ℝ (fun x => fderiv ℝ u x a) z :=
    fun a => h.clm_apply (differentiableAt_const _)
  have hs := hu.isSymmSndFDerivAt (by simp)
  have e : ∀ a b, del (fun x => del u x a) z b = (1 / 2 : ℂ) •
      (del (fun x => fderiv ℝ u x a) z b - I • del (fun x => fderiv ℝ u x (I • a)) z b) := by
    intro a b
    rw [show (fun x => del u x a) =
      fun x => (1 / 2 : ℂ) • (fderiv ℝ u x a - I • fderiv ℝ u x (I • a)) from rfl,
      del_const_smul _ ((h1 _).fun_sub ((h1 _).fun_const_smul I)),
      del_sub (h1 _) ((h1 _).fun_const_smul I), del_const_smul _ (h1 _)]
    rfl
  rw [e, e]
  simp only [del_apply, fderiv_fderiv_apply hu, smul_eq_mul]
  rw [hs.eq w, hs.eq w, hs.eq (I • w), hs.eq (I • w)]
  ring

theorem dbar_dbar_comm {u : E → ℂ} (hu : ContDiffAt ℝ 2 u z) (v w : E) :
    dbar (fun x => dbar u x v) z w = dbar (fun x => dbar u x w) z v := by
  have h := (differentiableAt_fderiv_of_contDiffAt_two hu)
  have h1 : ∀ a, DifferentiableAt ℝ (fun x => fderiv ℝ u x a) z :=
    fun a => h.clm_apply (differentiableAt_const _)
  have hs := hu.isSymmSndFDerivAt (by simp)
  have e : ∀ a b, dbar (fun x => dbar u x a) z b = (1 / 2 : ℂ) •
      (dbar (fun x => fderiv ℝ u x a) z b + I • dbar (fun x => fderiv ℝ u x (I • a)) z b) := by
    intro a b
    rw [show (fun x => dbar u x a) =
      fun x => (1 / 2 : ℂ) • (fderiv ℝ u x a + I • fderiv ℝ u x (I • a)) from rfl,
      dbar_const_smul _ ((h1 _).fun_add ((h1 _).fun_const_smul I)),
      dbar_add (h1 _) ((h1 _).fun_const_smul I), dbar_const_smul _ (h1 _)]
    rfl
  rw [e, e]
  simp only [dbar_apply, fderiv_fderiv_apply hu, smul_eq_mul]
  rw [hs.eq w, hs.eq w, hs.eq (I • w), hs.eq (I • w)]
  ring

theorem contDiffAt_del_at {u : E → ℂ} {j k : WithTop ℕ∞} (hu : ContDiffAt ℝ k u z)
    (hjk : j + 1 ≤ k) (ξ : E) : ContDiffAt ℝ j (fun x => del u x ξ) z :=
  MContDiffAt.mdel (A := fun x => (of fun _ _ => u x : Matrix Unit Unit ℂ)) (fun _ _ => hu) hjk ξ () ()

theorem contDiffAt_dbar_at {u : E → ℂ} {j k : WithTop ℕ∞} (hu : ContDiffAt ℝ k u z)
    (hjk : j + 1 ≤ k) (ξ : E) : ContDiffAt ℝ j (fun x => dbar u x ξ) z :=
  MContDiffAt.mdbar (A := fun x => (of fun _ _ => u x : Matrix Unit Unit ℂ)) (fun _ _ => hu) hjk ξ () ()

end Calc

end GlobalTheory.SecForm.DdcLoc
