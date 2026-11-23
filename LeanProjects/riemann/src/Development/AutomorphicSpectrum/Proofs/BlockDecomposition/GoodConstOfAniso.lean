import Mathlib
import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.CompanionTheory.RapidDecay

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {r : ℕ}

structure Good (U : Subgroup (GAd σ J)) (A : ℕ) (φ : GAd σ J → ℂ) : Prop where
  left : ∀ γ ∈ ratPts σ J, ∀ g, φ (γ * g) = φ g
  level : ∀ k ∈ U, k ∈ finPts σ J → ∀ g, φ (g * k) = φ g
  cont : Continuous φ
  smooth : GlobalTheory.UAut.IsSm σ J φ
  growth : ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) →
    ∃ C : ℝ, ∀ g, ‖l.foldr lineDer φ g‖ ≤ C * (height σ J g : ℝ) ^ A
  cusp : IsCuspidal σ J φ

def CloseInf (u : GAd σ J) (δ : ℝ) : Prop :=
  u ∈ infPts σ J ∧ ∀ (w : InfinitePlace F) (τ : EmbOver E w) (i j : Fin n),
    ‖(archMat σ J τ (projArch σ J w u) - 1) i j‖ ≤ δ

variable {σ J}

def pre (X : Matrix (Fin n) (Fin r) E) (s : Fin r) : Matrix (Fin n) (Fin (s.val + 1)) E :=
  X.submatrix id (Fin.castLE s.2)

def ratio (t : Fin r → ℝ) (s : Fin r) : ℝ :=
  if h : s.val + 1 < r then t s / t ⟨s.val + 1, h⟩ else t s

def rbar (t : Fin r → ℝ) : ℝ := Finset.univ.fold max 1 (ratio t)

theorem one_le_rbar (t : Fin r → ℝ) : 1 ≤ rbar t := Finset.le_fold_max _ |>.2 (Or.inl le_rfl)

theorem ratio_le_rbar (t : Fin r → ℝ) (s : Fin r) : ratio t s ≤ rbar t :=
  (Finset.le_fold_max _).2 (Or.inr ⟨s, Finset.mem_univ s, le_rfl⟩)

theorem rbar_eq (t : Fin r → ℝ) : rbar t = 1 ∨ ∃ s, rbar t = ratio t s := by
  have key : ∀ S : Finset (Fin r), S.fold max 1 (ratio t) = 1 ∨ ∃ s, S.fold max 1 (ratio t) = ratio t s := fun S => by
    induction S using Finset.induction_on with
    | empty => exact Or.inl (by simp)
    | insert a S ha ih =>
      rw [Finset.fold_insert ha]
      rcases max_choice (ratio t a) (S.fold max 1 (ratio t)) with e | e
      · exact Or.inr ⟨a, e⟩
      · rw [e]; exact ih
  exact key _

theorem ratio_pos {c : ℝ} {t : Fin r → ℝ} (ht : t ∈ cone r c) (s : Fin r) : 0 < ratio t s := by
  unfold ratio
  split_ifs with h
  · exact div_pos (ht.1 _) (ht.1 _)
  · exact ht.1 _

end GlobalTheory.CompanionTheory.RapidDecay

end
