import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TranslationInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatFormSmoothOnCover

set_option autoImplicit false

noncomputable section

open Matrix Set Filter Topology
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff

namespace GlobalTheory.TorsionForm

theorem wedge_add {m : ℕ} (i : Fin m) (w w' : Ext m) : wedge i (w + w') = wedge i w + wedge i w' := by
  funext S; simp only [wedge, Pi.add_apply]; split_ifs <;> ring

theorem wedge_smul {m : ℕ} (i : Fin m) (c : ℂ) (w : Ext m) : wedge i (c • w) = c • wedge i w := by
  funext S; simp only [wedge, Pi.smul_apply, smul_eq_mul]; split_ifs <;> ring

theorem contr_add {m : ℕ} (i : Fin m) (w w' : Ext m) : contr i (w + w') = contr i w + contr i w' := by
  funext S; simp only [contr, Pi.add_apply]; split_ifs <;> ring

theorem contr_smul {m : ℕ} (i : Fin m) (c : ℂ) (w : Ext m) : contr i (c • w) = c • contr i w := by
  funext S; simp only [contr, Pi.smul_apply, smul_eq_mul]; split_ifs <;> ring

def wedgeL {m : ℕ} (i : Fin m) : Ext m →L[ℂ] Ext m :=
  LinearMap.toContinuousLinearMap
    { toFun := wedge i, map_add' := wedge_add i, map_smul' := wedge_smul i }

def contrL {m : ℕ} (i : Fin m) : Ext m →L[ℂ] Ext m :=
  LinearMap.toContinuousLinearMap
    { toFun := contr i, map_add' := contr_add i, map_smul' := contr_smul i }

@[simp] theorem wedgeL_apply {m : ℕ} (i : Fin m) (w : Ext m) : wedgeL i w = wedge i w := rfl
@[simp] theorem contrL_apply {m : ℕ} (i : Fin m) (w : Ext m) : contrL i w = contr i w := rfl

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g n : ℕ}

def baseD (β : Fin n → E) (φ : E → ℂ) (b : E) (w : Ext (n + n + g)) : Ext (n + n + g) :=
  ∑ i, (wedge (dt g i) (d10 φ b (β i) • w) + wedge (dtb g i) (d01 φ b (β i) • w))

theorem superconn_congr (τ : E → Matrix (Fin g) (Fin g) ℂ) (h : Pt E g → ℝ) (β : Fin n → E) (u : ℝ)
    {s₁ s₂ : Pt E g → Ext (n + n + g)} {P : Pt E g} (hs : s₁ =ᶠ[𝓝 P] s₂) :
    superconn τ h β u s₁ P = superconn τ h β u s₂ P := by
  simp only [superconn, nablaE, dbarV, dbarAdj, pointDifference, d10, d01, hs.fderiv_eq, hs.eq_of_nhds]

theorem connForm_add (τ : E → Matrix (Fin g) (Fin g) ℂ) (b v : E) (w w' : Ext (n + n + g)) :
    connForm τ b v (w + w') = connForm τ b v w + connForm τ b v w' := by
  simp only [connForm, contr_add, wedge_add, smul_add, Finset.sum_add_distrib]

theorem connForm_smul (τ : E → Matrix (Fin g) (Fin g) ℂ) (b v : E) (c : ℂ) (w : Ext (n + n + g)) :
    connForm τ b v (c • w) = c • connForm τ b v w := by
  simp only [connForm, contr_smul, wedge_smul, Finset.smul_sum, smul_comm c]

section Add

variable {m : ℕ} {s₁ s₂ : Pt E g → Ext m} {P : Pt E g}

theorem dz_add_vector (h₁ : DifferentiableAt ℝ s₁ P) (h₂ : DifferentiableAt ℝ s₂ P) (v : Pt E g) :
    d10 (fun Q => s₁ Q + s₂ Q) P v = d10 s₁ P v + d10 s₂ P v := by
  unfold d10
  rw [fderiv_fun_add h₁ h₂]
  simp only [ContinuousLinearMap.add_apply, smul_add, smul_sub]
  abel

theorem dbar_add_vector (h₁ : DifferentiableAt ℝ s₁ P) (h₂ : DifferentiableAt ℝ s₂ P) (v : Pt E g) :
    d01 (fun Q => s₁ Q + s₂ Q) P v = d01 s₁ P v + d01 s₂ P v := by
  unfold d01
  rw [fderiv_fun_add h₁ h₂]
  simp only [ContinuousLinearMap.add_apply, smul_add]
  abel

end Add

section Add2

variable {s₁ s₂ : Pt E g → Ext (n + n + g)} {P : Pt E g}

theorem holomorphicConnection_add_section (h : Pt E g → ℝ) (h₁ : DifferentiableAt ℝ s₁ P) (h₂ : DifferentiableAt ℝ s₂ P)
    (v : Pt E g) :
    pointDifference (n := n) h (fun Q => s₁ Q + s₂ Q) P v = pointDifference h s₁ P v + pointDifference h s₂ P v := by
  unfold pointDifference
  rw [dz_add_vector h₁ h₂, smul_add]
  abel

theorem superconn_add (τ : E → Matrix (Fin g) (Fin g) ℂ) (h : Pt E g → ℝ) (β : Fin n → E) (u : ℝ)
    (h₁ : DifferentiableAt ℝ s₁ P) (h₂ : DifferentiableAt ℝ s₂ P) :
    superconn τ h β u (fun Q => s₁ Q + s₂ Q) P = superconn τ h β u s₁ P + superconn τ h β u s₂ P := by
  have e1 : nablaE τ h β (fun Q => s₁ Q + s₂ Q) P = nablaE τ h β s₁ P + nablaE τ h β s₂ P := by
    simp only [nablaE, holomorphicConnection_add_section h h₁ h₂, dbar_add_vector h₁ h₂, connForm_add, wedge_add,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    abel
  have e2 : dbarV (fun Q => s₁ Q + s₂ Q) P = dbarV s₁ P + dbarV s₂ P := by
    simp only [dbarV, dbar_add_vector h₁ h₂, wedge_add, ← Finset.sum_add_distrib]
  have e3 : dbarAdj τ h (fun Q => s₁ Q + s₂ Q) P = dbarAdj τ h s₁ P + dbarAdj τ h s₂ P := by
    simp only [dbarAdj, holomorphicConnection_add_section h h₁ h₂, contr_add, smul_add, Finset.sum_add_distrib, neg_add]
  simp only [superconn, e1, e2, e3, smul_add]
  abel

end Add2

end GlobalTheory.TorsionForm
