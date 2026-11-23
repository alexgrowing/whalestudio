import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GoodConstOfAniso

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RapidDecay
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal Topology

namespace GlobalTheory.CompanionTheory.RapidDecay

abbrev FrameIx (r : ℕ) : Type := Option (Fin r ⊕ Fin r)

variable {E : Type} [Field E] {n r : ℕ}

def frameIdem (S : E →+* E) (J : Matrix (Fin n) (Fin n) E) (X Y : Matrix (Fin n) (Fin r) E) :
    FrameIx r → Matrix (Fin n) (Fin n) E
  | some (Sum.inl i) => X * single i i (1 : E) * (cT S Y * J)
  | some (Sum.inr i) => Y * single i i (1 : E) * (cT S X * J)
  | none => 1 - X * (cT S Y * J) - Y * (cT S X * J)

def frameWt (t : Fin r → ℝ) : FrameIx r → ℝ
  | some (Sum.inl i) => t i
  | some (Sum.inr i) => (t i)⁻¹
  | none => 1

def frameLev (s : Fin r) : FrameIx r → ℕ
  | some (Sum.inl i) => if i ≤ s then 2 else 1
  | some (Sum.inr i) => if i ≤ s then 0 else 1
  | none => 1

theorem sum_frameIdem (S : E →+* E) (J : Matrix (Fin n) (Fin n) E) (X Y : Matrix (Fin n) (Fin r) E) :
    ∑ α, frameIdem S J X Y α = 1 := by
  have key : ∀ (A : Matrix (Fin n) (Fin r) E) (B : Matrix (Fin r) (Fin n) E),
      ∑ i : Fin r, (A * (Matrix.single i i (1 : E) : Matrix (Fin r) (Fin r) E) * B : Matrix (Fin n) (Fin n) E) = A * B := fun A B => by
    rw [← Matrix.sum_mul, ← Matrix.mul_sum, Matrix.sum_single_one, Matrix.mul_one]
  rw [Fintype.sum_option, Fintype.sum_sum_type]
  simp only [frameIdem]
  rw [key, key]
  abel

theorem frameWt_pos {t : Fin r → ℝ} (ht : ∀ i, 0 < t i) (α : FrameIx r) : 0 < frameWt t α := by
  rcases α with _ | i | i
  · exact one_pos
  · exact ht i
  · exact inv_pos.2 (ht i)

end GlobalTheory.CompanionTheory.RapidDecay

end
