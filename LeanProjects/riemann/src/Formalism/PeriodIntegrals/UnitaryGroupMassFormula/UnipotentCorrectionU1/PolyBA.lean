import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.CoreStar
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity

open Matrix
open scoped ComplexConjugate

noncomputable section

namespace PI.UnitaryCorollaryDerivatives

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.FourierDecayAlt.P.BetaSesquilinearity

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section pb

variable {k r : ℕ}

def PG (e : ℝ) (f : B.Mat k r → ℂ) : Prop :=
  ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f ∧ ∀ n : ℕ, ∃ C : ℝ, ∀ w : List (Bool × B.Mat k r),
    (∀ x ∈ w, B.unitLie k r x.2) → w.length ≤ n → ∀ g ∈ B.GV k r, ‖Dw w f g‖ ≤ C * B.gN g ^ e

lemma pb_ck {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : B.Mat k r → E} (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (m : ℕ∞) :
    B.CkOn m (B.GV k r) f := by
  intro g₀ _
  exact ⟨Set.univ, f, isOpen_univ, Set.mem_univ _,
    (hf.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffOn, fun _ _ _ => rfl⟩

lemma pb_nonneg {e : ℝ} {f : B.Mat k r → ℂ} (h : PG e f) (n : ℕ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ w : List (Bool × B.Mat k r), (∀ x ∈ w, B.unitLie k r x.2) → w.length ≤ n →
      ∀ g ∈ B.GV k r, ‖Dw w f g‖ ≤ C * B.gN g ^ e := by
  obtain ⟨C, hC⟩ := h.2 n
  refine ⟨max C 0, le_max_right _ _, fun w hw hl g hg => (hC w hw hl g hg).trans ?_⟩
  exact mul_le_mul_of_nonneg_right (le_max_left _ _)
    (Real.rpow_nonneg (by unfold B.gN; positivity) _)

lemma pb_mono {e e' : ℝ} {f : B.Mat k r → ℂ} (h : PG e f) (he : e ≤ e') : PG e' f := by
  refine ⟨h.1, fun n => ?_⟩
  obtain ⟨C, hC0, hC⟩ := pb_nonneg h n
  exact ⟨C, fun w hw hl g hg => (hC w hw hl g hg).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (gN_ge_one hg) he) hC0)⟩

private theorem Dw_const_zero (w : List (Bool × B.Mat k r)) :
    Dw w (fun _ : B.Mat k r => (0 : ℂ)) = fun _ => 0 := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    have h' : List.foldr Dx (fun _ : B.Mat k r => (0 : ℂ)) w = fun _ => 0 := ih
    simp only [Dw, List.foldr, Dx, h']
    split_ifs <;> funext g <;> simp [B.LdV, RdV]

lemma pb_zero (e : ℝ) : PG e (fun _ : B.Mat k r => (0 : ℂ)) := by
  unfold PG
  refine ⟨contDiff_const, fun n => ⟨0, fun w _ _ g _ => ?_⟩⟩
  rw [Dw_const_zero]
  simp

lemma pb_Dw_const (c : ℂ) (w : List (Bool × B.Mat k r)) :
    ∃ c' : ℂ, ‖c'‖ ≤ ‖c‖ ∧ Dw w (fun _ => c) = fun _ => c' := by
  induction w with
  | nil => exact ⟨c, le_rfl, rfl⟩
  | cons x w ih =>
    obtain ⟨c', -, h⟩ := ih
    refine ⟨0, by simp, ?_⟩
    have h' : List.foldr Dx (fun _ => c) w = fun _ => c' := h
    simp only [Dw, List.foldr, Dx, h']
    split_ifs <;> funext g <;> simp [B.LdV, RdV]

lemma pb_const (c : ℂ) : PG 0 (fun _ : B.Mat k r => c) := by
  unfold PG
  refine ⟨contDiff_const, fun n => ⟨‖c‖, fun w _ _ g _ => ?_⟩⟩
  obtain ⟨c', hc', h⟩ := pb_Dw_const (k := k) (r := r) c w
  rw [h, Real.rpow_zero, mul_one]
  exact hc'

lemma pb_add {e : ℝ} {f h : B.Mat k r → ℂ} (hf : PG e f) (hh : PG e h) :
    PG e (fun g => f g + h g) := by
  refine ⟨hf.1.add hh.1, fun n => ?_⟩
  obtain ⟨C₁, hC₁⟩ := hf.2 n
  obtain ⟨C₂, hC₂⟩ := hh.2 n
  refine ⟨C₁ + C₂, fun w hw hl g hg => ?_⟩
  have hw' : ∀ x ∈ w, B.inLie k r x.2 := fun x hx => (hw x hx).1
  rw [Dw_add hw' (pb_ck hf.1 _) (pb_ck hh.1 _) g hg, add_mul]
  exact (norm_add_le _ _).trans (add_le_add (hC₁ w hw hl g hg) (hC₂ w hw hl g hg))

lemma pb_Dw_mulL {w : List (Bool × B.Mat k r)} (hw : ∀ x ∈ w, B.inLie k r x.2) {f : B.Mat k r → ℂ}
    (hf : B.CkOn w.length (B.GV k r) f) :
    ∀ g ∈ B.GV k r, Dw w (fun g => ContinuousLinearMap.mul ℂ ℂ (f g)) g =
      ContinuousLinearMap.mul ℂ ℂ (Dw w f g) := by
  induction w with
  | nil => intro g _; rfl
  | cons x w ih =>
    have hw' : ∀ y ∈ w, B.inLie k r y.2 := fun y hy => hw y (by simp [hy])
    have hle : ((w.length : ℕ) : ℕ∞) ≤ ((x :: w).length : ℕ) := by exact_mod_cast Nat.le_succ _
    have e : (1 : ℕ∞) + (w.length : ℕ∞) = ((x :: w).length : ℕ) := by
      push_cast [List.length_cons]; ring
    intro g hg
    show Dx x (Dw w _) g = ContinuousLinearMap.mul ℂ ℂ (Dx x (Dw w f) g)
    rw [Dx_congr (hw x (by simp)) (ih hw' (sCkOn_mono hle hf)) g hg]
    have h1 := CkOn_diff (hw x (by simp)) (CkOn_Dw hw' (m := 1) (by rw [e]; exact hf)) hg hg
    have h2 := ((ContinuousLinearMap.mul ℂ ℂ).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
    rw [Dx_eq]
    exact h2.deriv

lemma pb_mul {e₁ e₂ : ℝ} {f h : B.Mat k r → ℂ} (hf : PG e₁ f) (hh : PG e₂ h) :
    PG (e₁ + e₂) (fun g => f g * h g) := by
  have hcd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun g => ContinuousLinearMap.mul ℂ ℂ (f g)) :=
    ((ContinuousLinearMap.mul ℂ ℂ).restrictScalars ℝ).contDiff.comp hf.1
  refine ⟨hf.1.mul hh.1, fun n => ?_⟩
  obtain ⟨C₁, hC₁0, hC₁⟩ := pb_nonneg hf n
  obtain ⟨C₂, hC₂0, hC₂⟩ := pb_nonneg hh n
  refine ⟨2 ^ n * (C₁ * C₂), fun w hw hl g hg => ?_⟩
  have hw' : ∀ x ∈ w, B.inLie k r x.2 := fun x hx => (hw x hx).1
  have hP : Pr (∅ : Set (B.Mat k r)) (B.GV k r) w.length
      (fun g => ContinuousLinearMap.mul ℂ ℂ (f g)) h :=
    ⟨pb_ck hcd _, pb_ck hh.1 _, fun _ _ hg => hg.elim⟩
  have hp := gN_pos hg
  have hp1 : 0 ≤ B.gN g ^ e₁ := Real.rpow_nonneg hp.le _
  have hp2 : 0 ≤ B.gN g ^ e₂ := Real.rpow_nonneg hp.le _
  have hM : 0 ≤ C₁ * B.gN g ^ e₁ * (C₂ * B.gN g ^ e₂) :=
    mul_nonneg (mul_nonneg hC₁0 hp1) (mul_nonneg hC₂0 hp2)
  have hb := leib_bound isOpen_empty (fun g hg => Or.inr hg) g hg (C₁ * B.gN g ^ e₁ * (C₂ * B.gN g ^ e₂)) w
    (fun g => ContinuousLinearMap.mul ℂ ℂ (f g)) h hw' hP (by
      intro w₁ w₂ h₁ h₂ _
      have u1 : ∀ x ∈ w₁, B.unitLie k r x.2 := fun x hx => hw x (h₁.subset hx)
      have u2 : ∀ x ∈ w₂, B.unitLie k r x.2 := fun x hx => hw x (h₂.subset hx)
      rw [pb_Dw_mulL (fun x hx => (u1 x hx).1) (pb_ck hf.1 _) g hg]
      exact mul_le_mul ((ContinuousLinearMap.opNorm_mul_apply_le _ _ _).trans
          (hC₁ w₁ u1 (h₁.length_le.trans hl) g hg))
        (hC₂ w₂ u2 (h₂.length_le.trans hl) g hg) (norm_nonneg _) (mul_nonneg hC₁0 hp1))
  have e1 : (fun g => f g * h g) = ap (fun g => ContinuousLinearMap.mul ℂ ℂ (f g)) h := by
    funext g; simp [ap]
  rw [e1]
  refine hb.trans ?_
  rw [Real.rpow_add hp]
  have h2 : (2 : ℝ) ^ w.length ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hl
  calc (2 : ℝ) ^ w.length * (C₁ * B.gN g ^ e₁ * (C₂ * B.gN g ^ e₂))
      ≤ 2 ^ n * (C₁ * B.gN g ^ e₁ * (C₂ * B.gN g ^ e₂)) := mul_le_mul_of_nonneg_right h2 hM
    _ = 2 ^ n * (C₁ * C₂) * (B.gN g ^ e₁ * B.gN g ^ e₂) := by ring

end pb

end PI.UnitaryCorollaryDerivatives
