import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowersMulZero

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

namespace GlobalTheory.RadCov

theorem mul_eq_zero_of_mulVec_mulVec {p q n : ℕ} {A : Matrix (Fin p) (Fin n) ℂ}
    {B : Matrix (Fin n) (Fin q) ℂ} (h : ∀ x, A *ᵥ (B *ᵥ x) = 0) : A * B = 0 := by
  ext i j
  have hx := congrFun (h (Pi.single j 1)) i
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_single_one] at hx
  simpa using hx

theorem Biorth.col_mem {n m : ℕ} {W : ℕ → Submodule ℂ (Fin n → ℂ)} {r : ℕ → ℕ}
    {T : ∀ b, Matrix (Fin n) (Fin (r b)) ℂ} {T' : ∀ b, Matrix (Fin (r b)) (Fin n) ℂ}
    (hT : Biorth r m T T') (hW : ∀ k y, y ∈ W k ↔ ∀ b, k ≤ b → T' b *ᵥ y = 0)
    (s k : ℕ) (hk : s < k) (x : Fin (r s) → ℂ) : T s *ᵥ x ∈ W k := by
  rw [hW]
  intro b hb
  rw [Matrix.mulVec_mulVec, hT.2.1 b s (by omega), Matrix.zero_mulVec]

theorem Biorth.mul_eq_block {n m p q : ℕ} {W : ℕ → Submodule ℂ (Fin n → ℂ)} {r : ℕ → ℕ}
    {T : ∀ b, Matrix (Fin n) (Fin (r b)) ℂ} {T' : ∀ b, Matrix (Fin (r b)) (Fin n) ℂ}
    (hT : Biorth r m T T') (hW : ∀ k y, y ∈ W k ↔ ∀ b, k ≤ b → T' b *ᵥ y = 0)
    (b : ℕ) {A : Matrix (Fin p) (Fin n) ℂ} {B : Matrix (Fin n) (Fin q) ℂ}
    (hA : ∀ y ∈ W b, A *ᵥ y = 0) (hB : ∀ x, B *ᵥ x ∈ W (b + 1)) :
    A * B = (A * T b) * (T' b * B) := by
  have hAT : ∀ c, c < b → A * T c = 0 := fun c hc =>
    mul_eq_zero_of_mulVec_mulVec fun x => hA _ (Biorth.col_mem hT hW c b hc x)
  have hTB : ∀ c, b < c → T' c * B = 0 := fun c hc =>
    mul_eq_zero_of_mulVec_mulVec fun x => (hW (b + 1) _).1 (hB x) c (by omega)
  calc A * B = A * (∑ c ∈ Finset.range m, T c * T' c) * B := by rw [hT.2.2, Matrix.mul_one]
    _ = ∑ c ∈ Finset.range m, (A * T c) * (T' c * B) := by
      rw [Matrix.mul_sum, Matrix.sum_mul]
      simp only [Matrix.mul_assoc]
    _ = (A * T b) * (T' b * B) := by
      apply Finset.sum_eq_single b
      · intro c _ hcb
        rcases lt_or_gt_of_ne hcb with hc | hc
        · rw [hAT c hc, Matrix.zero_mul]
        · rw [hTB c hc, Matrix.mul_zero]
      · intro hb

        have hTb : T b = 0 := by
          rw [← Matrix.one_mul (T b), ← hT.2.2, Matrix.sum_mul]
          apply Finset.sum_eq_zero
          intro c hc
          rw [Matrix.mul_assoc, hT.2.1 c b (by rintro rfl; exact hb hc), Matrix.mul_zero]
        rw [hTb, Matrix.mul_zero, Matrix.zero_mul]

theorem blockFrames_triangular (n m : ℕ) (W : ℕ → Submodule ℂ (Fin n → ℂ)) (r : ℕ → ℕ)
    (T U : ∀ b, Matrix (Fin n) (Fin (r b)) ℂ) (T' U' : ∀ b, Matrix (Fin (r b)) (Fin n) ℂ)
    (hT : Biorth r m T T') (hU : Biorth r m U U')
    (hWT : ∀ k y, y ∈ W k ↔ ∀ b, k ≤ b → T' b *ᵥ y = 0)
    (hWU : ∀ k y, y ∈ W k ↔ ∀ b, k ≤ b → U' b *ᵥ y = 0) :
    (∀ b, (U' b * T b) * (T' b * U b) = 1) ∧ ∀ c, ∀ Y ∈ lowers W c, ∀ b,
      U' b * Y * U (b + c + 1) =
        (U' b * T b) * (T' b * Y * T (b + c + 1)) * (T' (b + c + 1) * U (b + c + 1)) := by
  refine ⟨fun b => ?_, fun c Y hY b => ?_⟩
  · rw [← Biorth.mul_eq_block hT hWT b (fun y hy => (hWU b y).1 hy b le_rfl)
      (fun x => Biorth.col_mem hU hWU b (b + 1) (by omega) x)]
    exact hU.1 b
  · have hY' : ∀ b', ∀ y ∈ W (b' + c + 1), Y *ᵥ y ∈ W b' := mem_lowers.1 hY
    have e1 : U' b * (Y * U (b + c + 1)) = (U' b * T b) * (T' b * (Y * U (b + c + 1))) :=
      Biorth.mul_eq_block hT hWT b (fun y hy => (hWU b y).1 hy b le_rfl) (fun x => by
        rw [← Matrix.mulVec_mulVec]
        exact hY' (b + 1) _ (Biorth.col_mem hU hWU (b + c + 1) (b + 1 + c + 1) (by omega) x))
    have e2 : (T' b * Y) * U (b + c + 1) =
        ((T' b * Y) * T (b + c + 1)) * (T' (b + c + 1) * U (b + c + 1)) :=
      Biorth.mul_eq_block hT hWT (b + c + 1)
        (fun y hy => by
          rw [← Matrix.mulVec_mulVec]
          exact (hWT b _).1 (hY' b y hy) b le_rfl)
        (fun x => Biorth.col_mem hU hWU (b + c + 1) (b + c + 1 + 1) (by omega) x)
    calc U' b * Y * U (b + c + 1) = U' b * (Y * U (b + c + 1)) := Matrix.mul_assoc _ _ _
      _ = (U' b * T b) * (T' b * (Y * U (b + c + 1))) := e1
      _ = (U' b * T b) * ((T' b * Y) * U (b + c + 1)) := by rw [Matrix.mul_assoc (T' b)]
      _ = _ := by rw [e2]; simp only [Matrix.mul_assoc]

end GlobalTheory.RadCov
