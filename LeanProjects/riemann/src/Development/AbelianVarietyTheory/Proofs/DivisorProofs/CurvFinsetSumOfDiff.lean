import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TranslationInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullFullL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarAddVectorScalar

set_option autoImplicit false

noncomputable section

open Matrix MeasureTheory Set Filter Topology
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.OneVec
open scoped Real ContDiff

namespace GlobalTheory.TorsionForm.OneVec

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g n : ℕ}

theorem superconn_zero (τ : E → Matrix (Fin g) (Fin g) ℂ) (h : Pt E g → ℝ) (β : Fin n → E) (u : ℝ)
    (P : Pt E g) : superconn τ h β u (fun _ => (0 : Ext (n + n + g))) P = 0 := by
  simp [superconn, nablaE, dbarV, dbarAdj, pointDifference, d10, d01, Pullback.connForm_zero,
    Pullback.contr_zero, Pullback.wedge_zero]

theorem superconn_finset_sum (τ : E → Matrix (Fin g) (Fin g) ℂ) (h : Pt E g → ℝ) (β : Fin n → E)
    (u : ℝ) {ι : Type} (s : Finset ι) (F : ι → Pt E g → Ext (n + n + g)) (P : Pt E g)
    (hF : ∀ i ∈ s, DifferentiableAt ℝ (F i) P) :
    superconn τ h β u (fun Q => ∑ i ∈ s, F i Q) P = ∑ i ∈ s, superconn τ h β u (F i) P := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using superconn_zero τ h β u P
  | insert a s ha ih =>
    have e : (fun Q => ∑ i ∈ insert a s, F i Q) = fun Q => F a Q + ∑ i ∈ s, F i Q := by
      funext Q; rw [Finset.sum_insert ha]
    have hs : DifferentiableAt ℝ (fun Q => ∑ i ∈ s, F i Q) P :=
      DifferentiableAt.fun_sum fun i hi => hF i (Finset.mem_insert_of_mem hi)
    rw [e, Pullback.superconn_add τ h β u (hF a (Finset.mem_insert_self a s)) hs,
      ih fun i hi => hF i (Finset.mem_insert_of_mem hi), Finset.sum_insert ha]

theorem curv_finset_sum_of_diff (τ : E → Matrix (Fin g) (Fin g) ℂ) (h : Pt E g → ℝ) (β : Fin n → E)
    (b : E) (u : ℝ) {ι : Type} (s : Finset ι) (G : ι → (Fin g → ℂ) → Ext (n + n + g))
    (hG : ∀ i, Differentiable ℝ (G i)) (z : Fin g → ℂ)
    (hd : ∀ i ∈ s, DifferentiableAt ℝ (superconn τ h β u fun P : Pt E g => G i P.2) (b, z)) :
    curv τ h β b u (fun y => ∑ i ∈ s, G i y) z = ∑ i ∈ s, curv τ h β b u (G i) z := by
  have inner : (superconn τ h β u fun P : Pt E g => ∑ i ∈ s, G i P.2) =
      fun P => ∑ i ∈ s, superconn τ h β u (fun P : Pt E g => G i P.2) P := by
    funext P
    exact superconn_finset_sum τ h β u s (fun i (P : Pt E g) => G i P.2) P
      fun i _ => ((hG i) P.2).comp P differentiableAt_snd
  simp only [curv]
  rw [inner]
  exact superconn_finset_sum τ h β u s _ (b, z) hd

end GlobalTheory.TorsionForm.OneVec
