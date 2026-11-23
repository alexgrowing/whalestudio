import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetHsBall
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

namespace GlobalTheory.IwConst.FlagTrace

variable {n a : ℕ} {ε : Fin n → Bool} {W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)}

theorem mem_lowers {X : Matrix (Fin n) (Fin n) ℂ} : X ∈ lowers ε W ↔
    ((∀ i : Fin a, ∀ y ∈ W i.succ, X *ᵥ y ∈ W i.castSucc) ∧
      ∀ y ∈ perp ε (W (Fin.last a)), X *ᵥ y ∈ W (Fin.last a)) ∧
      ∀ i : Fin a, ∀ y ∈ perp ε (W i.castSucc), X *ᵥ y ∈ perp ε (W i.succ) := by
  simp only [lowers, Submodule.mem_inf, Submodule.mem_iInf, mem_into]

theorem mem_keeps {X : Matrix (Fin n) (Fin n) ℂ} : X ∈ keeps ε W ↔
    (∀ i, ∀ y ∈ W i, X *ᵥ y ∈ W i) ∧ ∀ i, ∀ y ∈ perp ε (W i), X *ᵥ y ∈ perp ε (W i) := by
  simp only [keeps, Submodule.mem_inf, Submodule.mem_iInf, mem_into]

theorem perp_anti {V V' : Submodule ℂ (Fin n → ℂ)} (h : V ≤ V') : perp ε V' ≤ perp ε V :=
  fun _ hy x hx => hy x (h hx)

theorem mul_mem_lowers {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lowers ε W) (hY : Y ∈ keeps ε W) :
    X * Y ∈ lowers ε W := by
  rw [mem_lowers] at hX ⊢
  rw [mem_keeps] at hY
  simp only [← Matrix.mulVec_mulVec]
  exact ⟨⟨fun i y hy => hX.1.1 i _ (hY.1 _ y hy), fun y hy => hX.1.2 _ (hY.2 _ y hy)⟩,
    fun i y hy => hX.2 i _ (hY.2 _ y hy)⟩

theorem isNilpotent_of_mem_lowers (h0 : W 0 = ⊥) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lowers ε W) :
    IsNilpotent X := by
  rw [mem_lowers] at hX
  have h1 : ∀ i : Fin (a + 1), ∀ y, X ^ (i : ℕ) *ᵥ y ∈ perp ε (W i) := by
    intro i
    induction i using Fin.induction with
    | zero => intro y x hx; rw [h0, Submodule.mem_bot] at hx; simp [hx]
    | succ i ih =>
      intro y
      rw [Fin.val_succ, pow_succ', ← Matrix.mulVec_mulVec]
      exact hX.2 i _ (ih y)
  have h2 : ∀ i : Fin (a + 1), ∀ y ∈ W i, X ^ (i : ℕ) *ᵥ y = 0 := by
    intro i
    induction i using Fin.induction with
    | zero => intro y hy; rw [h0, Submodule.mem_bot] at hy; simp [hy]
    | succ i ih =>
      intro y hy
      rw [Fin.val_succ, pow_succ, ← Matrix.mulVec_mulVec]
      exact ih _ (hX.1.1 i y hy)
  refine ⟨a + 1 + a, ?_⟩
  refine Matrix.toLin'.injective (LinearMap.ext fun y => ?_)
  rw [Matrix.toLin'_apply, map_zero, LinearMap.zero_apply, pow_add, pow_succ, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec]
  exact h2 (Fin.last a) _ (hX.1.2 _ (h1 (Fin.last a) y))

theorem lowers_le_keeps {j : Fin a → ℕ} (h : IsIsoFlag ε j W) : lowers ε W ≤ keeps ε W := by
  obtain ⟨h0, hm, -, hi⟩ := h
  intro X hX
  rw [mem_lowers] at hX
  rw [mem_keeps]
  refine ⟨fun i => ?_, fun i => ?_⟩
  · induction i using Fin.cases with
    | zero => intro y hy; rw [h0, Submodule.mem_bot] at hy; simp [hy]
    | succ i => exact fun y hy => hm (Fin.castSucc_le_succ i) (hX.1.1 i y hy)
  · induction i using Fin.lastCases with
    | last => exact fun y hy x hx => hi x hx _ (hX.1.2 y hy)
    | cast i => exact fun y hy => perp_anti (hm (Fin.castSucc_le_succ i)) (hX.2 i y hy)

theorem trace_lowers_keeps : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ)
    (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), IsIsoFlag ε j W →
    (∀ X ∈ lowers ε W, ∀ Y ∈ keeps ε W, (X * Y).trace = 0) ∧ lowers ε W ≤ keeps ε W ∧
      (1 : Matrix (Fin n) (Fin n) ℂ) ∈ keeps ε W ∧ ∀ X ∈ keeps ε W, ∀ Y ∈ keeps ε W, X * Y ∈ keeps ε W := by
  intro n ε a j W h
  refine ⟨fun X hX Y hY => ?_, lowers_le_keeps h, ?_, fun X hX Y hY => ?_⟩
  · exact (Matrix.isNilpotent_trace_of_isNilpotent
      (isNilpotent_of_mem_lowers h.1 (mul_mem_lowers hX hY))).eq_zero
  · rw [mem_keeps]; simp
  · rw [mem_keeps] at hX hY ⊢
    simp only [← Matrix.mulVec_mulVec]
    exact ⟨fun i y hy => hX.1 i _ (hY.1 i y hy), fun i y hy => hX.2 i _ (hY.2 i y hy)⟩

end GlobalTheory.IwConst.FlagTrace
