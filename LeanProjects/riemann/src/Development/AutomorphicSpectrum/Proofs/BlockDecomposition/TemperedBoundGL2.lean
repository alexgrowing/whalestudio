import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces

noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.DualHol

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

def TemperedBoundGL3 (W : GL (Fin 3) F → ℂ) : Prop :=
  Continuous W ∧ ∀ ε : ℝ, 0 < ε → ε < 1 / 2 → ∃ C B : ℝ, ∀ (t₁ t₂ t₃ : Fˣ), ∀ k ∈ GLnLocal.integralGL F 3,
    ‖W (dg t₁ t₂ t₃ * k)‖ ≤ C * (modulus ((t₁ / t₃ : Fˣ) : F) : ℝ) ^ (1 - ε) ∧
      (W (dg t₁ t₂ t₃ * k) ≠ 0 →
        (modulus ((t₁ / t₂ : Fˣ) : F) : ℝ) ≤ B ∧ (modulus ((t₂ / t₃ : Fˣ) : F) : ℝ) ≤ B)

def TemperedBoundGL2 (W : GL (Fin 2) F → ℂ) : Prop :=
  Measurable W ∧ ∀ ε : ℝ, 0 < ε → ε < 1 / 2 → ∃ C B : ℝ, ∀ (x y : Fˣ), ∀ k ∈ GLnLocal.integralGL F 2,
    ‖W (dg2 x y * k)‖ ≤ C * (modulus ((x / y : Fˣ) : F) : ℝ) ^ (1 / 2 - ε) ∧
      (W (dg2 x y * k) ≠ 0 → (modulus ((x / y : Fˣ) : F) : ℝ) ≤ B)

theorem TemperedBoundGL3.zero : TemperedBoundGL3 (0 : GL (Fin 3) F → ℂ) :=
  ⟨continuous_const, fun _ _ _ => ⟨0, 0, fun _ _ _ _ _ => by simp⟩⟩

theorem TemperedBoundGL2.zero : TemperedBoundGL2 (0 : GL (Fin 2) F → ℂ) :=
  ⟨measurable_const, fun _ _ _ => ⟨0, 0, fun _ _ _ _ => by simp⟩⟩

theorem TemperedBoundGL3.add {W W' : GL (Fin 3) F → ℂ} (h : TemperedBoundGL3 W) (h' : TemperedBoundGL3 W') : TemperedBoundGL3 (W + W') := by
  refine ⟨h.1.add h'.1, fun ε h0 h1 => ?_⟩
  obtain ⟨C, B, hb⟩ := h.2 ε h0 h1
  obtain ⟨C', B', hb'⟩ := h'.2 ε h0 h1
  refine ⟨C + C', max B B', fun t₁ t₂ t₃ k hk => ⟨?_, fun hne => ?_⟩⟩
  · have e1 := (hb t₁ t₂ t₃ k hk).1
    have e2 := (hb' t₁ t₂ t₃ k hk).1
    calc ‖(W + W') (dg t₁ t₂ t₃ * k)‖ ≤ ‖W (dg t₁ t₂ t₃ * k)‖ + ‖W' (dg t₁ t₂ t₃ * k)‖ := norm_add_le _ _
      _ ≤ _ := by rw [add_mul]; exact add_le_add e1 e2
  · by_cases hz : W (dg t₁ t₂ t₃ * k) = 0
    · have hz' : W' (dg t₁ t₂ t₃ * k) ≠ 0 := by
        intro h2; apply hne; simp [hz, h2]
      obtain ⟨a, b⟩ := (hb' t₁ t₂ t₃ k hk).2 hz'
      exact ⟨a.trans (le_max_right _ _), b.trans (le_max_right _ _)⟩
    · obtain ⟨a, b⟩ := (hb t₁ t₂ t₃ k hk).2 hz
      exact ⟨a.trans (le_max_left _ _), b.trans (le_max_left _ _)⟩

theorem TemperedBoundGL2.add {W W' : GL (Fin 2) F → ℂ} (h : TemperedBoundGL2 W) (h' : TemperedBoundGL2 W') : TemperedBoundGL2 (W + W') := by
  refine ⟨h.1.add h'.1, fun ε h0 h1 => ?_⟩
  obtain ⟨C, B, hb⟩ := h.2 ε h0 h1
  obtain ⟨C', B', hb'⟩ := h'.2 ε h0 h1
  refine ⟨C + C', max B B', fun x y k hk => ⟨?_, fun hne => ?_⟩⟩
  · have e1 := (hb x y k hk).1
    have e2 := (hb' x y k hk).1
    calc ‖(W + W') (dg2 x y * k)‖ ≤ ‖W (dg2 x y * k)‖ + ‖W' (dg2 x y * k)‖ := norm_add_le _ _
      _ ≤ _ := by rw [add_mul]; exact add_le_add e1 e2
  · by_cases hz : W (dg2 x y * k) = 0
    · have hz' : W' (dg2 x y * k) ≠ 0 := by
        intro h2; apply hne; simp [hz, h2]
      exact ((hb' x y k hk).2 hz').trans (le_max_right _ _)
    · exact ((hb x y k hk).2 hz).trans (le_max_left _ _)

theorem TemperedBoundGL3.smul {W : GL (Fin 3) F → ℂ} (c : ℂ) (h : TemperedBoundGL3 W) : TemperedBoundGL3 (c • W) := by
  refine ⟨h.1.const_smul c, fun ε h0 h1 => ?_⟩
  obtain ⟨C, B, hb⟩ := h.2 ε h0 h1
  refine ⟨‖c‖ * C, B, fun t₁ t₂ t₃ k hk => ⟨?_, fun hne => ?_⟩⟩
  · rw [Pi.smul_apply, norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hb t₁ t₂ t₃ k hk).1 (norm_nonneg _)
  · refine (hb t₁ t₂ t₃ k hk).2 fun hz => hne ?_
    simp [hz]

theorem TemperedBoundGL2.smul {W : GL (Fin 2) F → ℂ} (c : ℂ) (h : TemperedBoundGL2 W) : TemperedBoundGL2 (c • W) := by
  refine ⟨h.1.const_smul c, fun ε h0 h1 => ?_⟩
  obtain ⟨C, B, hb⟩ := h.2 ε h0 h1
  refine ⟨‖c‖ * C, B, fun x y k hk => ⟨?_, fun hne => ?_⟩⟩
  · rw [Pi.smul_apply, norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hb x y k hk).1 (norm_nonneg _)
  · refine (hb x y k hk).2 fun hz => hne ?_
    simp [hz]

theorem TemperedBoundGL3.span {S : Set (GL (Fin 3) F → ℂ)} (h : ∀ W ∈ S, TemperedBoundGL3 W) {W : GL (Fin 3) F → ℂ}
    (hW : W ∈ Submodule.span ℂ S) : TemperedBoundGL3 W := by
  induction hW using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => exact TemperedBoundGL3.zero
  | add x y _ _ hx hy => exact hx.add hy
  | smul c x _ hx => exact hx.smul c

theorem TemperedBoundGL2.span {S : Set (GL (Fin 2) F → ℂ)} (h : ∀ W ∈ S, TemperedBoundGL2 W) {W : GL (Fin 2) F → ℂ}
    (hW : W ∈ Submodule.span ℂ S) : TemperedBoundGL2 W := by
  induction hW using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => exact TemperedBoundGL2.zero
  | add x y _ _ hx hy => exact hx.add hy
  | smul c x _ hx => exact hx.smul c

end GlobalTheory.CompanionTheory.DualHol
