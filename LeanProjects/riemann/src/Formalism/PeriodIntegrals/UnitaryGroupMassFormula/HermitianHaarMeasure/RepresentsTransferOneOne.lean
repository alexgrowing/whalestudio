import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianHaarMeasure.RepOnOfEq

open Matrix Finset MeasureTheory
open scoped ContDiff

noncomputable section

namespace PI.QnHermHaar

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Gen

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {i : Fin (r + 1)} {μ : Measure (Mt k r)}

theorem repTm (H : Hyp k r z z' i μ) (w : ℂ) (a b : Fin (mdim k r i)) :
    RepOn (hI H) (Tm (EA H) w a b) (Top (EH k r) w (posL k r i a) (posL k r i b)) := by
  have h := repOn_add (hI H) (repOn_ite (hI H) (a = b) (repOn_algebraMap (hI H) w) (repOn_zero (hI H)))
    (repE H a b)
  unfold Tm
  refine repOn_of_eq h fun f => ?_
  funext g
  by_cases hab : a = b
  · subst hab; simp [Formalism.QuantumDeterminants.Top, EOp]
  · have : posL k r i a ≠ posL k r i b := fun h => hab (posL_inj h)
    simp [Formalism.QuantumDeterminants.Top, EOp, hab, this]

theorem repQminor (H : Hyp k r z z' i μ) {t : ℕ} (a b : Fin t → Fin (mdim k r i)) (w : ℂ) :
    RepOn (hI H) (qminor (EA H) a b w) (qminorOp (EH k r) (posL k r i ∘ a) (posL k r i ∘ b) w) := by
  unfold qminor
  exact repOn_sum (hI H) Finset.univ fun σ _ => repOn_mul (hI H) (repOn_intCast (hI H) _)
    (repOn_list (hI H) t _ _ fun k' => repTm H _ _ _)

theorem represents_transfer_zero_zero (H : Hyp k r z z' i μ) (Y : ℂ) :
    RepOn (hI H) (tA (EA H) (YA H) (YbA H) (xv k r z' i) (xbv k r z' i) (uC k r i Y) 0 0)
      (tL k r z z' i Y 0 0) :=
  repQminor H id id _

theorem represents_transfer_zero_one (H : Hyp k r z z' i μ) (Y : ℂ) :
    RepOn (hI H) (tA (EA H) (YA H) (YbA H) (xv k r z' i) (xbv k r z' i) (uC k r i Y) 0 1)
      (tL k r z z' i Y 0 1) := by
  have h := repOn_neg (hI H) (repOn_sum (hI H) (Finset.univ : Finset (Fin (mdim k r i))) fun a _ => repOn_sum (hI H) (Finset.univ : Finset (Fin (mdim k r i))) fun b _ =>
    repOn_smul (hI H) ((-1 : ℂ) ^ ((a : ℕ) + (b : ℕ)) * xv k r z' i b)
      (repOn_mul (hI H) (repYb H a) (repQminor H (skip1 a) (skip1 b) (uC k r i Y - 1))))
  refine repOn_of_eq h fun f => ?_
  funext g
  simp only [tL, chatL, MOp, Pi.neg_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  ring

theorem represents_transfer_one_zero (H : Hyp k r z z' i μ) (Y : ℂ) :
    RepOn (hI H) (tA (EA H) (YA H) (YbA H) (xv k r z' i) (xbv k r z' i) (uC k r i Y) 1 0)
      (tL k r z z' i Y 1 0) := by
  have h := repOn_neg (hI H) (repOn_sum (hI H) (Finset.univ : Finset (Fin (mdim k r i))) fun a _ => repOn_sum (hI H) (Finset.univ : Finset (Fin (mdim k r i))) fun b _ =>
    repOn_smul (hI H) ((-1 : ℂ) ^ ((a : ℕ) + (b : ℕ)) * xbv k r z' i a)
      (repOn_mul (hI H) (repY H b) (repQminor H (skip1 a) (skip1 b) (uC k r i Y))))
  refine repOn_of_eq h fun f => ?_
  funext g
  simp only [tL, chatL, MOp, Pi.neg_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  ring

theorem tA_11 {A : Type*} [Ring A] [Algebra ℂ A] {m : ℕ} (E : Fin m → Fin m → A) (Y Yb : Fin m → A)
    (x xb : Fin m → ℂ) (u : ℂ) : tA E Y Yb x xb u 1 1 = -∑ i : Fin m, ∑ i' : Fin m, ∑ j : Fin m, ∑ j' : Fin m,
      if i < i' ∧ j < j' then
        ((-1 : ℂ) ^ ((i : ℕ) + (i' : ℕ) + (j : ℕ) + (j' : ℕ))) •
          ((Yb i * algebraMap ℂ A (xb i') - Yb i' * algebraMap ℂ A (xb i)) *
            (Y j * algebraMap ℂ A (x j') - Y j' * algebraMap ℂ A (x j)) *
            qminor E (skip2 i i') (skip2 j j') (u - 1))
      else 0 := rfl

theorem represents_transfer_one_one (H : Hyp k r z z' i μ) (Y : ℂ) :
    RepOn (hI H) (tA (EA H) (YA H) (YbA H) (xv k r z' i) (xbv k r z' i) (uC k r i Y) 1 1)
      (tL k r z z' i Y 1 1) := by
  have h := repOn_neg (hI H) (repOn_sum (hI H) (Finset.univ : Finset (Fin (mdim k r i))) fun a _ => repOn_sum (hI H) (Finset.univ : Finset (Fin (mdim k r i))) fun a' _ =>
    repOn_sum (hI H) (Finset.univ : Finset (Fin (mdim k r i))) fun b _ => repOn_sum (hI H) (Finset.univ : Finset (Fin (mdim k r i))) fun b' _ =>
    repOn_ite (hI H) (a < a' ∧ b < b')
      (repOn_smul (hI H) ((-1 : ℂ) ^ ((a : ℕ) + (a' : ℕ) + (b : ℕ) + (b' : ℕ)))
        (repOn_mul (hI H)
          (repOn_mul (hI H)
            (repOn_sub (hI H) (repOn_mul (hI H) (repYb H a) (repOn_algebraMap (hI H) (xbv k r z' i a')))
              (repOn_mul (hI H) (repYb H a') (repOn_algebraMap (hI H) (xbv k r z' i a))))
            (repOn_sub (hI H) (repOn_mul (hI H) (repY H b) (repOn_algebraMap (hI H) (xv k r z' i b')))
              (repOn_mul (hI H) (repY H b') (repOn_algebraMap (hI H) (xv k r z' i b)))))
          (repQminor H (skip2 a a') (skip2 b b') (uC k r i Y - 1))))
      (repOn_zero (hI H)))
  rw [tA_11]
  refine repOn_of_eq h fun f => ?_
  funext g
  simp only [tL, chat2L, Pi.neg_apply, Finset.sum_apply]
  rw [neg_inj]
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro a' _
  apply Finset.sum_congr rfl; intro b _
  apply Finset.sum_congr rfl; intro b' _
  split_ifs
  · simp only [MOp, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  · rfl

theorem rep_tL (H : Hyp k r z z' i μ) (Y : ℂ) (p q : Fin 2) :
    RepOn (hI H) (tA (EA H) (YA H) (YbA H) (xv k r z' i) (xbv k r z' i) (uC k r i Y) p q)
      (tL k r z z' i Y p q) := by
  fin_cases p <;> fin_cases q
  · exact represents_transfer_zero_zero H Y
  · exact represents_transfer_zero_one H Y
  · exact represents_transfer_one_zero H Y
  · exact represents_transfer_one_one H Y

theorem uC_star (Y : ℂ) : star (uC k r i Y) = uC k r i (star Y) := by
  simp [uC]

theorem glue_holds_var : Glue := by
  intro hAlg hET hEA hMT hTI hYb hXb hHm hEP hGl hYL k r z z' i μ hμ hz hz' f₁ f₂ hs₁ hs₂ hc₁ hc₂ Y a b
  have H : Hyp k r z z' i μ := ⟨hμ, hz, hz', hET, hEA, hMT, hTI, hYb, hXb, hHm, hEP, hGl, hYL⟩
  have hstar := hAlg (A (hI H)) (mdim k r i) (EA H) (YA H) (YbA H) (Hm k r i) (xv k r z' i) (xbv k r z' i)
    (glRel_A H) (hHm k r i).1 (hHm k r i).2 (starE_A H) (yComm H) (ybComm H) (yybComm H) (eyComm H) (eybComm H)
    (ybStar H) (hXb k r z' i hz') (uC k r i Y) a b
  have hT := rep_tL H Y a b
  have hS : RepOn (hI H) (star (tA (EA H) (YA H) (YbA H) (xv k r z' i) (xbv k r z' i) (uC k r i Y) a b))
      (tL k r z z' i (star Y) b a) := by
    rw [hstar, uC_star]
    exact rep_tL H (star Y) b a
  exact pr_of_repOn (hI H) hT hS (mem_testSub.2 ⟨hs₁, hc₁⟩) (mem_testSub.2 ⟨hs₂, hc₂⟩)

end PI.QnHermHaar
