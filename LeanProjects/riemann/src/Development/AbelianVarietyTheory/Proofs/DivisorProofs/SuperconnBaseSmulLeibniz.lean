import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicConnectionAddSection
open Matrix Set Filter Topology GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm
open scoped Real ContDiff

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TorsionForm.Leibniz

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g m : ℕ}

theorem fderiv_fst_smul {φ : E → ℂ} {σ : Pt E g → Ext m} {P : Pt E g}
    (hφ : DifferentiableAt ℝ φ P.1) (hσ : DifferentiableAt ℝ σ P) (w : Pt E g) :
    fderiv ℝ (fun Q : Pt E g => φ Q.1 • σ Q) P w =
      φ P.1 • fderiv ℝ σ P w + fderiv ℝ φ P.1 w.1 • σ P := by
  have h1 : HasFDerivAt (fun Q : Pt E g => φ Q.1)
      ((fderiv ℝ φ P.1).comp (ContinuousLinearMap.fst ℝ E (Fin g → ℂ))) P :=
    hφ.hasFDerivAt.comp P hasFDerivAt_fst
  have h2 : HasFDerivAt (fun Q : Pt E g => φ Q.1 • σ Q) _ P := h1.smul hσ.hasFDerivAt
  rw [h2.fderiv]
  simp

theorem d10_smul_base_leibniz_of_differentiableAt {φ : E → ℂ} {σ : Pt E g → Ext m} {P : Pt E g}
    (hφ : DifferentiableAt ℝ φ P.1) (hσ : DifferentiableAt ℝ σ P) (v : Pt E g) :
    d10 (fun Q : Pt E g => φ Q.1 • σ Q) P v = φ P.1 • d10 σ P v + d10 φ P.1 v.1 • σ P := by
  unfold d10
  rw [fderiv_fst_smul hφ hσ, fderiv_fst_smul hφ hσ]
  simp only [Prod.smul_fst, smul_add, smul_sub, smul_smul, sub_smul]
  funext S
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem d01_smul_base_leibniz_of_differentiableAt {φ : E → ℂ} {σ : Pt E g → Ext m} {P : Pt E g}
    (hφ : DifferentiableAt ℝ φ P.1) (hσ : DifferentiableAt ℝ σ P) (v : Pt E g) :
    d01 (fun Q : Pt E g => φ Q.1 • σ Q) P v = φ P.1 • d01 σ P v + d01 φ P.1 v.1 • σ P := by
  unfold d01
  rw [fderiv_fst_smul hφ hσ, fderiv_fst_smul hφ hσ]
  funext S
  simp only [Prod.smul_fst, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_smul]
  ring

theorem d10_apply_zero_direction (φ : E → ℂ) (b : E) : d10 φ b 0 = 0 := by simp [d10]

theorem d01_apply_zero_direction (φ : E → ℂ) (b : E) : d01 φ b 0 = 0 := by simp [d01]

end GlobalTheory.TorsionForm.Leibniz

open GlobalTheory.TorsionForm.Leibniz in
theorem GlobalTheory.TorsionForm.superconn_fst_smul : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g n : ℕ}
    (τ : E → Matrix (Fin g) (Fin g) ℂ) (h : Pt E g → ℝ) (β : Fin n → E) (u : ℝ) {φ : E → ℂ}
    {σ : Pt E g → Ext (n + n + g)} {P : Pt E g}, DifferentiableAt ℝ φ P.1 → DifferentiableAt ℝ σ P →
    superconn τ h β u (fun Q => φ Q.1 • σ Q) P = φ P.1 • superconn τ h β u σ P + baseD β φ P.1 (σ P) := by
  intro E _ _ g n τ h β u φ σ P hφ hσ
  have hn : ∀ v, pointDifference (n := n) h (fun Q => φ Q.1 • σ Q) P v =
      φ P.1 • pointDifference h σ P v + d10 φ P.1 v.1 • σ P := by
    intro v
    unfold pointDifference
    rw [d10_smul_base_leibniz_of_differentiableAt hφ hσ, smul_add, smul_comm (d10 _ P v) (φ P.1) (σ P)]
    abel
  have e1 : nablaE τ h β (fun Q => φ Q.1 • σ Q) P = φ P.1 • nablaE τ h β σ P + baseD β φ P.1 (σ P) := by
    simp only [nablaE, baseD, hn, d01_smul_base_leibniz_of_differentiableAt hφ hσ, connForm_smul, wedge_add, wedge_smul,
      Finset.smul_sum, smul_add, ← Finset.sum_add_distrib, hor]
    refine Finset.sum_congr rfl fun i _ => ?_
    abel
  have e2 : dbarV (fun Q => φ Q.1 • σ Q) P = φ P.1 • dbarV σ P := by
    simp only [dbarV, d01_smul_base_leibniz_of_differentiableAt hφ hσ, vert, d01_apply_zero_direction, zero_smul, add_zero, wedge_smul,
      Finset.smul_sum]
  have e3 : dbarAdj τ h (fun Q => φ Q.1 • σ Q) P = φ P.1 • dbarAdj τ h σ P := by
    simp only [dbarAdj, hn, vert, d10_apply_zero_direction, zero_smul, add_zero, contr_smul, Finset.smul_sum,
      smul_neg, smul_comm (φ P.1)]
  simp only [superconn, e1, e2, e3, smul_add, smul_comm (φ P.1) (Real.sqrt u : ℂ)]
  abel
