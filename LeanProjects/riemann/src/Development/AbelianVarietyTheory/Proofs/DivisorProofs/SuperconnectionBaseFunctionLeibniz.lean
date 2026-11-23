import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameAtApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarAddVectorScalar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DBaseApply

set_option autoImplicit false

noncomputable section

open Matrix MeasureTheory Set Filter Topology GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.Gauge
  GlobalTheory.TorsionForm.Fibrewise
open scoped ContDiff

namespace GlobalTheory.TorsionForm.Leibniz

open GlobalTheory.TorsionForm.Pullback

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g n : ℕ}

theorem contr_smul {m : ℕ} (i : Fin m) (c : ℂ) (w : Ext m) : contr i (c • w) = c • contr i w := by
  funext S; simp only [contr, Pi.smul_apply, smul_eq_mul]; split_ifs <;> ring

theorem connForm_smul (τ : E → Matrix (Fin g) (Fin g) ℂ) (b v : E) (c : ℂ) (w : Ext (n + n + g)) :
    connForm τ b v (c • w) = c • connForm τ b v w := by
  simp only [connForm, contr_smul, wedge_smul, Finset.smul_sum, smul_comm c]

theorem fderiv_fsmul {c : Pt E g → ℂ} {r : Pt E g → Ext (n + n + g)} {P : Pt E g}
    (hc : DifferentiableAt ℝ c P) (hr : DifferentiableAt ℝ r P) (w : Pt E g) :
    fderiv ℝ (fun Q => c Q • r Q) P w = c P • fderiv ℝ r P w + fderiv ℝ c P w • r P := by
  rw [fderiv_fun_smul hc hr]
  simp

theorem d10_smul_eq_add_of_differentiableAt {c : Pt E g → ℂ} {r : Pt E g → Ext (n + n + g)} {P : Pt E g}
    (hc : DifferentiableAt ℝ c P) (hr : DifferentiableAt ℝ r P) (w : Pt E g) :
    d10 (fun Q => c Q • r Q) P w = c P • d10 r P w + d10 c P w • r P := by
  simp only [d10, fderiv_fsmul hc hr, smul_eq_mul]
  module

theorem d01_smul_eq_add_of_differentiableAt {c : Pt E g → ℂ} {r : Pt E g → Ext (n + n + g)} {P : Pt E g}
    (hc : DifferentiableAt ℝ c P) (hr : DifferentiableAt ℝ r P) (w : Pt E g) :
    d01 (fun Q => c Q • r Q) P w = c P • d01 r P w + d01 c P w • r P := by
  simp only [d01, fderiv_fsmul hc hr, smul_eq_mul]
  module

theorem fderiv_fst_comp {ψ : E → ℂ} {P : Pt E g} (hψ : DifferentiableAt ℝ ψ P.1) (w : Pt E g) :
    fderiv ℝ (fun Q : Pt E g => ψ Q.1) P w = fderiv ℝ ψ P.1 w.1 := by
  have : HasFDerivAt (fun Q : Pt E g => ψ Q.1) ((fderiv ℝ ψ P.1).comp (ContinuousLinearMap.fst ℝ E (Fin g → ℂ))) P :=
    hψ.hasFDerivAt.comp P (hasFDerivAt_fst)
  rw [this.fderiv]; rfl

theorem d10_comp_fst_eq_of_differentiableAt {ψ : E → ℂ} {P : Pt E g} (hψ : DifferentiableAt ℝ ψ P.1) (w : Pt E g) :
    d10 (fun Q : Pt E g => ψ Q.1) P w = d10 ψ P.1 w.1 := by
  simp only [d10, fderiv_fst_comp hψ, Prod.smul_fst]

theorem d01_comp_fst_eq_of_differentiableAt {ψ : E → ℂ} {P : Pt E g} (hψ : DifferentiableAt ℝ ψ P.1) (w : Pt E g) :
    d01 (fun Q : Pt E g => ψ Q.1) P w = d01 ψ P.1 w.1 := by
  simp only [d01, fderiv_fst_comp hψ, Prod.smul_fst]

section Main

variable (τ : E → Matrix (Fin g) (Fin g) ℂ) (h : Pt E g → ℝ) (β : Fin n → E)
  {ψ : E → ℂ} {r : Pt E g → Ext (n + n + g)} {P : Pt E g}

theorem nab10_base_smul_eq_add_of_differentiableAt (hψ : DifferentiableAt ℝ ψ P.1) (hr : DifferentiableAt ℝ r P) (w : Pt E g) :
    pointDifference h (fun Q => ψ Q.1 • r Q) P w = ψ P.1 • pointDifference h r P w + d10 ψ P.1 w.1 • r P := by
  have hc : DifferentiableAt ℝ (fun Q : Pt E g => ψ Q.1) P := hψ.comp P differentiableAt_fst
  simp only [pointDifference, d10_smul_eq_add_of_differentiableAt hc hr, d10_comp_fst_eq_of_differentiableAt hψ, smul_add, smul_comm (ψ P.1)]
  abel

theorem d01_base_smul_section_eq_add (hψ : DifferentiableAt ℝ ψ P.1) (hr : DifferentiableAt ℝ r P) (w : Pt E g) :
    d01 (fun Q => ψ Q.1 • r Q) P w = ψ P.1 • d01 r P w + d01 ψ P.1 w.1 • r P := by
  have hc : DifferentiableAt ℝ (fun Q : Pt E g => ψ Q.1) P := hψ.comp P differentiableAt_fst
  rw [d01_smul_eq_add_of_differentiableAt hc hr, d01_comp_fst_eq_of_differentiableAt hψ]

theorem d10_apply_zero_vector (b : E) : d10 ψ b 0 = 0 := by simp [d10]

theorem d01_zero_direction_eq_zero (b : E) : d01 ψ b 0 = 0 := by simp [d01]

theorem nablaE_fsmul (hψ : DifferentiableAt ℝ ψ P.1) (hr : DifferentiableAt ℝ r P) :
    nablaE τ h β (fun Q => ψ Q.1 • r Q) P = ψ P.1 • nablaE τ h β r P + dBase β ψ P.1 (r P) := by
  simp only [nablaE, dBase, nab10_base_smul_eq_add_of_differentiableAt h hψ hr, d01_base_smul_section_eq_add hψ hr, connForm_smul, Finset.smul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [hor, wedge_add, wedge_smul, smul_add]
  abel

theorem dbarV_fsmul (hψ : DifferentiableAt ℝ ψ P.1) (hr : DifferentiableAt ℝ r P) :
    dbarV (fun Q => ψ Q.1 • r Q) P = ψ P.1 • dbarV r P := by
  simp only [dbarV, d01_base_smul_section_eq_add hψ hr, vert, d01_zero_direction_eq_zero, zero_smul, add_zero, wedge_smul,
    Finset.smul_sum]

theorem dbarAdj_fsmul (hψ : DifferentiableAt ℝ ψ P.1) (hr : DifferentiableAt ℝ r P) :
    dbarAdj τ h (fun Q => ψ Q.1 • r Q) P = ψ P.1 • dbarAdj τ h r P := by
  simp only [dbarAdj, nab10_base_smul_eq_add_of_differentiableAt h hψ hr, vert, d10_apply_zero_vector, zero_smul, add_zero, contr_smul,
    Finset.smul_sum, smul_neg, smul_comm (ψ P.1)]

end Main

theorem superconn_fsmul (τ : E → Matrix (Fin g) (Fin g) ℂ) (h : Pt E g → ℝ) (β : Fin n → E)
    (u : ℝ) (ψ : E → ℂ) (r : Pt E g → Ext (n + n + g)) (P : Pt E g)
    (hψ : DifferentiableAt ℝ ψ P.1) (hr : DifferentiableAt ℝ r P) :
    superconn τ h β u (fun Q => ψ Q.1 • r Q) P = ψ P.1 • superconn τ h β u r P + dBase β ψ P.1 (r P) := by
  simp only [superconn, nablaE_fsmul τ h β hψ hr, dbarV_fsmul hψ hr, dbarAdj_fsmul τ h hψ hr,
    smul_add, smul_comm (ψ P.1) (Real.sqrt u : ℂ)]
  abel

end GlobalTheory.TorsionForm.Leibniz
