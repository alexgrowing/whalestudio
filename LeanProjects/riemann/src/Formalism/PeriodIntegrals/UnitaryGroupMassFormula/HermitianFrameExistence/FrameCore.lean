import Mathlib
import Formalism.PeriodIntegrals.ScPiExists
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianFrameExistence.HJSumSmulRight
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianFrameExistence.PosOfPerp

noncomputable section

open Matrix

namespace PI.ScPiFrameW

open PI.ScPiExists

variable {n : ℕ}

theorem gs_step (ε : Fin n → Bool) {r k : ℕ} (hn : n = 2 * r + k + 1) (σ : Fin (r + 1) → Fin n)
    (hσ : ∀ i, ε i = false → ∃ j, σ j = i)
    (e f : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (t : ℝ) (ht : 0 < t)
    (hee : ∀ a b, hJ ε (e a) (e b) = 0) (hff : ∀ a b, hJ ε (f a) (f b) = 0)
    (hef : ∀ a b, hJ ε (e a) (f b) = if a = b then 1 else 0)
    (hez : ∀ a, hJ ε (e a) z = 0) (hfz : ∀ a, hJ ε (f a) z = 0) (hzz : hJ ε z z = -(t : ℂ))
    (m : ℕ) (hm : m < k) (w : Fin m → Fin n → ℂ)
    (hwo : ∀ a b, hJ ε (w a) (w b) = if a = b then 1 else 0)
    (hwp : ∀ a, (∀ c, hJ ε (e c) (w a) = 0 ∧ hJ ε (f c) (w a) = 0) ∧ hJ ε z (w a) = 0) :
    ∃ w' : Fin (m + 1) → Fin n → ℂ, (∀ a b, hJ ε (w' a) (w' b) = if a = b then 1 else 0) ∧
      ∀ a, (∀ c, hJ ε (e c) (w' a) = 0 ∧ hJ ε (f c) (w' a) = 0) ∧ hJ ε z (w' a) = 0 := by
  obtain ⟨y, hy, hperp⟩ := exists_perp ε
    (Sum.elim e (Sum.elim f (Sum.elim (fun _ : Unit => z) w)))
    (by simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]; omega)
  have hey : ∀ c, hJ ε (e c) y = 0 := fun c => hperp (Sum.inl c)
  have hfy : ∀ c, hJ ε (f c) y = 0 := fun c => hperp (Sum.inr (Sum.inl c))
  have hzy : hJ ε z y = 0 := hperp (Sum.inr (Sum.inr (Sum.inl ())))
  have hwy : ∀ a, hJ ε (w a) y = 0 := fun a => hperp (Sum.inr (Sum.inr (Sum.inr a)))
  have hs0 : 0 < (hJ ε y y).re :=
    pos_of_perp ε σ hσ e f z t ht hee hff hef hez hfz hzz y hey hfy hzy hy
  obtain ⟨s, hs_eq⟩ : ∃ s : ℝ, s = (hJ ε y y).re := ⟨_, rfl⟩
  have hs : 0 < s := hs_eq ▸ hs0
  have hyy : hJ ε y y = (s : ℂ) := by
    rw [hs_eq, hJ_self, Complex.ofReal_re]
  have hμ : star (((Real.sqrt s)⁻¹ : ℝ) : ℂ) * ((((Real.sqrt s)⁻¹ : ℝ) : ℂ) * hJ ε y y) = 1 := by
    rw [hyy, show star (((Real.sqrt s)⁻¹ : ℝ) : ℂ) = (starRingEnd ℂ) (((Real.sqrt s)⁻¹ : ℝ) : ℂ)
      from rfl, Complex.conj_ofReal]
    have hsq : Real.sqrt s * Real.sqrt s = s := Real.mul_self_sqrt hs.le
    have h1 : (Real.sqrt s)⁻¹ * ((Real.sqrt s)⁻¹ * s) = 1 := by
      rw [← mul_assoc, ← mul_inv, hsq, inv_mul_cancel₀ hs.ne']
    exact_mod_cast h1
  refine ⟨Fin.cons ((((Real.sqrt s)⁻¹ : ℝ) : ℂ) • y) w, ?_, ?_⟩
  · intro a b
    refine Fin.cases ?_ (fun a' => ?_) a <;> refine Fin.cases ?_ (fun b' => ?_) b
    · rw [if_pos rfl]
      simp only [Fin.cons_zero, hJ_smul_left, hJ_smul_right]
      rw [mul_left_comm]
      exact hμ
    · rw [if_neg (Fin.succ_ne_zero b').symm]
      simp only [Fin.cons_zero, Fin.cons_succ, hJ_smul_left, hJ_conj ε (w b') y, hwy, star_zero,
        mul_zero]
    · rw [if_neg (Fin.succ_ne_zero a')]
      simp only [Fin.cons_zero, Fin.cons_succ, hJ_smul_right, hwy, mul_zero]
    · simp only [Fin.cons_succ, Fin.succ_inj]
      exact hwo a' b'
  · intro a
    refine Fin.cases ?_ (fun a' => ?_) a
    · simp [hJ_smul_right, hey, hfy, hzy]
    · simp only [Fin.cons_succ]
      exact hwp a'

theorem frame_core (ε : Fin n → Bool) {r k : ℕ} (hn : n = 2 * r + k + 1) (σ : Fin (r + 1) → Fin n)
    (hσ : ∀ i, ε i = false → ∃ j, σ j = i)
    (e f : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (t : ℝ) (ht : 0 < t)
    (hee : ∀ a b, hJ ε (e a) (e b) = 0) (hff : ∀ a b, hJ ε (f a) (f b) = 0)
    (hef : ∀ a b, hJ ε (e a) (f b) = if a = b then 1 else 0)
    (hez : ∀ a, hJ ε (e a) z = 0) (hfz : ∀ a, hJ ε (f a) z = 0) (hzz : hJ ε z z = -(t : ℂ)) :
    ∃ w : Fin k → Fin n → ℂ, (∀ a b, hJ ε (w a) (w b) = if a = b then 1 else 0) ∧
      ∀ a, (∀ c, hJ ε (e c) (w a) = 0 ∧ hJ ε (f c) (w a) = 0) ∧ hJ ε z (w a) = 0 := by
  have key : ∀ m, m ≤ k → ∃ w : Fin m → Fin n → ℂ,
      (∀ a b, hJ ε (w a) (w b) = if a = b then 1 else 0) ∧
      ∀ a, (∀ c, hJ ε (e c) (w a) = 0 ∧ hJ ε (f c) (w a) = 0) ∧ hJ ε z (w a) = 0 := by
    intro m
    induction m with
    | zero => intro _; exact ⟨fun a => a.elim0, fun a => a.elim0, fun a => a.elim0⟩
    | succ m ih =>
      intro hm
      obtain ⟨w, h1, h2⟩ := ih (by omega)
      exact gs_step ε hn σ hσ e f z t ht hee hff hef hez hfz hzz m (by omega) w h1 h2
  exact key k le_rfl

end PI.ScPiFrameW
