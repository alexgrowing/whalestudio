import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TranslationInv
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAddFundamentalDomainLatticeDomain
open Matrix MeasureTheory Set Filter Topology
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm
open scoped Real ContDiff

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SuperconnLinear

section Alg

variable {m : ℕ}

theorem wedge_add (i : Fin m) (v w : Ext m) : wedge i (v + w) = wedge i v + wedge i w := by
  funext S; by_cases hS : i ∈ S <;> simp [wedge, hS, mul_add]

theorem wedge_smul (i : Fin m) (c : ℂ) (w : Ext m) : wedge i (c • w) = c • wedge i w := by
  funext S; by_cases hS : i ∈ S <;> simp [wedge, hS, mul_left_comm]

theorem contr_add (i : Fin m) (v w : Ext m) : contr i (v + w) = contr i v + contr i w := by
  funext S; by_cases hS : i ∈ S <;> simp [contr, hS, mul_add]

theorem contr_smul (i : Fin m) (c : ℂ) (w : Ext m) : contr i (c • w) = c • contr i w := by
  funext S; by_cases hS : i ∈ S <;> simp [contr, hS, mul_left_comm]

end Alg

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g n : ℕ}
  (τ : E → Matrix (Fin g) (Fin g) ℂ) (h : Pt E g → ℝ) (β : Fin n → E)

theorem connForm_add (b v : E) (w w' : Ext (n + n + g)) :
    connForm (n := n) τ b v (w + w') = connForm τ b v w + connForm τ b v w' := by
  simp [connForm, contr_add, wedge_add, smul_add, Finset.sum_add_distrib]

theorem connForm_smul (b v : E) (c : ℂ) (w : Ext (n + n + g)) :
    connForm (n := n) τ b v (c • w) = c • connForm τ b v w := by
  simp [connForm, contr_smul, wedge_smul, Finset.smul_sum, smul_comm c]

variable {F G : Pt E g → Ext (n + n + g)} {P : Pt E g}

theorem dz_add_vector (hF : DifferentiableAt ℝ F P) (hG : DifferentiableAt ℝ G P) (v : Pt E g) :
    d10 (fun Q => F Q + G Q) P v = d10 F P v + d10 G P v := by
  simp only [d10, fderiv_fun_add hF hG, ContinuousLinearMap.add_apply, smul_add]
  module

theorem dbar_add_vector (hF : DifferentiableAt ℝ F P) (hG : DifferentiableAt ℝ G P) (v : Pt E g) :
    d01 (fun Q => F Q + G Q) P v = d01 F P v + d01 G P v := by
  simp only [d01, fderiv_fun_add hF hG, ContinuousLinearMap.add_apply, smul_add]
  module

theorem d10_smul (hF : DifferentiableAt ℝ F P) (c : ℂ) (v : Pt E g) :
    d10 (fun Q => c • F Q) P v = c • d10 F P v := by
  simp only [d10, fderiv_fun_const_smul hF c, ContinuousLinearMap.smul_apply, smul_sub, smul_comm c]

theorem d01_smul (hF : DifferentiableAt ℝ F P) (c : ℂ) (v : Pt E g) :
    d01 (fun Q => c • F Q) P v = c • d01 F P v := by
  simp only [d01, fderiv_fun_const_smul hF c, ContinuousLinearMap.smul_apply, smul_add, smul_comm c]

theorem superconn_add (u : ℝ) (hF : DifferentiableAt ℝ F P) (hG : DifferentiableAt ℝ G P) :
    superconn τ h β u (fun Q => F Q + G Q) P = superconn τ h β u F P + superconn τ h β u G P := by
  simp only [superconn, nablaE, pointDifference, dbarV, dbarAdj, dz_add_vector hF hG, dbar_add_vector hF hG, connForm_add,
    wedge_add, contr_add, smul_add, Finset.sum_add_distrib, neg_add]
  abel

theorem connection_smul (hF : DifferentiableAt ℝ F P) (c : ℂ) (v : Pt E g) :
    pointDifference h (fun Q => c • F Q) P v = c • pointDifference h F P v := by
  simp only [pointDifference, d10_smul hF, smul_add]
  rw [smul_comm c]

theorem superconn_smul (u : ℝ) (hF : DifferentiableAt ℝ F P) (c : ℂ) :
    superconn τ h β u (fun Q => c • F Q) P = c • superconn τ h β u F P := by
  simp only [superconn, nablaE, dbarV, dbarAdj, connection_smul h hF, d01_smul hF, connForm_smul,
    wedge_add, contr_add, wedge_smul, contr_smul, smul_add, Finset.smul_sum, smul_neg, smul_comm c]

theorem superconn_zero (u : ℝ) (P : Pt E g) :
    superconn τ h β u (fun _ => (0 : Ext (n + n + g))) P = 0 := by
  have w0 : ∀ {m : ℕ} (i : Fin m), wedge i (0 : Ext m) = 0 := fun i => by
    simpa using wedge_smul i 0 0
  have c0 : ∀ {m : ℕ} (i : Fin m), contr i (0 : Ext m) = 0 := fun i => by
    simpa using contr_smul i 0 0
  have f0 : ∀ b v, connForm (n := n) τ b v 0 = 0 := fun b v => by
    simpa using connForm_smul τ b v 0 0
  simp [superconn, nablaE, pointDifference, dbarV, dbarAdj, d10, d01, w0, c0, f0]

theorem superconn_sum (u : ℝ) {ι : Type} (s : Finset ι) (a : ι → ℂ)
    (F : ι → Pt E g → Ext (n + n + g)) (P : Pt E g) (hF : ∀ i ∈ s, DifferentiableAt ℝ (F i) P) :
    superconn τ h β u (fun Q => ∑ i ∈ s, a i • F i Q) P = ∑ i ∈ s, a i • superconn τ h β u (F i) P := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using superconn_zero τ h β u P
  | insert j s hj ih =>
    have hF' : ∀ i ∈ s, DifferentiableAt ℝ (F i) P := fun i hi => hF i (Finset.mem_insert_of_mem hi)
    have hd : DifferentiableAt ℝ (fun Q => ∑ i ∈ s, a i • F i Q) P :=
      DifferentiableAt.fun_sum fun i hi => (hF' i hi).const_smul (a i)
    simp only [Finset.sum_insert hj]
    rw [superconn_add τ h β u (F := fun Q => a j • F j Q)
      (show DifferentiableAt ℝ (fun Q => a j • F j Q) P from
        (hF j (Finset.mem_insert_self j s)).const_smul (a j)) hd,
      superconn_smul τ h β u (hF j (Finset.mem_insert_self j s)), ih hF']

end GlobalTheory.SuperconnLinear

theorem GlobalTheory.superconn_linear : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g n : ℕ}
    (τ : E → Matrix (Fin g) (Fin g) ℂ) (h : Pt E g → ℝ) (β : Fin n → E) (u : ℝ) {ι : Type}
    (s : Finset ι) (a : ι → ℂ) (F : ι → Pt E g → Ext (n + n + g)) (P : Pt E g),
    (∀ i ∈ s, DifferentiableAt ℝ (F i) P) →
      superconn τ h β u (fun Q => ∑ i ∈ s, a i • F i Q) P = ∑ i ∈ s, a i • superconn τ h β u (F i) P :=
  fun τ h β u _ s a F P hF => GlobalTheory.SuperconnLinear.superconn_sum τ h β u s a F P hF
