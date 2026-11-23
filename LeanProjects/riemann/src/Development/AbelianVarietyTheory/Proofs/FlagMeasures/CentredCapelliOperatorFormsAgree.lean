import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Admissible

open Formalism.FourierDecayAlt GlobalTheory.ThA MeasureTheory Formalism.QuantumDeterminants Matrix
open scoped InnerProductSpace

namespace GlobalTheory.ThA

theorem qminorOp_eq_qdetOp_of_val {n t : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Eop : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → E) → (Matrix (Fin n) (Fin n) ℂ → E))
    (h : t = n) (p : Fin t → Fin n) (hp : ∀ j, (p j).val = j.val) (u : ℂ)
    (f : Matrix (Fin n) (Fin n) ℂ → E) : qminorOp Eop p p u f = qdetOp Eop u f := by
  subst h
  have e : p = id := funext fun j => Fin.ext (hp j)
  rw [e]
  rfl

theorem centredCapelli_forms_agree :
    ∀ (k r : ℕ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (Y : ℂ) (F : B.Mat k r → V),
      Q.CV k r Y F = PI.CapelliEig.capC (k := k) (r := r) Y F ∧
        Q.CV k r Y F = Formalism.MainNotions.S.capC (k := k) (r := r) Y F := by
  intro k r V _ _ Y F
  have hm : Q.mdim k r 0 = 2 * r + k + 1 := by simp [Q.mdim]
  have hu : Q.uC k r 0 Y = Y + ((2 * r + k : ℕ) : ℂ) / 2 := by
    unfold Q.uC
    rw [hm]
    push_cast
    ring
  have key : Q.CV k r Y F = capelliH (Hpk k r) (Y + ((2 * r + k : ℕ) : ℂ) / 2) F := by
    unfold Q.CV Q.capL capelliH
    rw [hu]
    exact qminorOp_eq_qdetOp_of_val _ hm _ (fun j => by simp [Q.posL]) _ _
  exact ⟨key, key⟩

end GlobalTheory.ThA
