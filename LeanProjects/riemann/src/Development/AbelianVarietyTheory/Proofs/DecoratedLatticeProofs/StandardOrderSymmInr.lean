import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnesRepresent

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum

noncomputable section
namespace GlobalTheory.SymChain.NonZeroAt

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Coords
variable {ι ι' n n' : Type*} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c c' : ℕ}

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem typeFrame_bas_val (ϖ : kˣ) (ord : ι ≃ n ⊕ Fin c) :
    (typeFrame ϖ ord).bas.val = diagonal (Sum.elim (fun _ => (1 : k)) fun i : Fin c => (ϖ : k) ^ (i.val + 1)) := by
  change (fromBlocks 1 0 0 (diagonal _) : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) = _
  rw [← diagonal_one, fromBlocks_diagonal]
  congr 1

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem typeFrame_bas_inv_val (ϖ : kˣ) (ord : ι ≃ n ⊕ Fin c) :
    ((typeFrame ϖ ord).bas⁻¹).val =
      diagonal (Sum.elim (fun _ => (1 : k)) fun i : Fin c => ((ϖ : k) ^ (i.val + 1))⁻¹) := by
  refine Units.inv_eq_of_mul_eq_one_right ?_
  rw [typeFrame_bas_val, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  rcases i with i | i
  · simp
  · simp [mul_inv_cancel₀, pow_ne_zero]

end Coords

section Ord
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

end Ord

section Chain
variable {s κ : ℕ} (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
variable (k) in

def Est (j : ℕ) : Matrix (Ix (Fin κ ⊕ Fin (s + 1)) t (j + 1)) (Ix (Fin κ ⊕ Fin (s + 1)) t j) k :=
  fun P Q => if P = ixSucc _ t j (.inl Q) then 1 else 0

def xst (j c : ℕ) (h : j + c = s) :
    Matrix (XIx (Fin κ) t (j + 1) ⊕ Fin c) (XIx (Fin κ) t j ⊕ Fin (c + 1)) k :=
  (typeFrame S.ϖ (stdOrd (Fin κ) t (l := s + 1) (j + 1) c (by omega))).bas.val *
    (Est k (κ := κ) (s := s) t j).submatrix (stdOrd (Fin κ) t (l := s + 1) (j + 1) c (by omega)).symm
      (stdOrd (Fin κ) t (l := s + 1) j (c + 1) (by omega)).symm *
    ((typeFrame S.ϖ (stdOrd (Fin κ) t (l := s + 1) j (c + 1) (by omega))).bas⁻¹).val

end Chain

section Entry
variable {s κ : ℕ} (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t]

end Entry

section Main
variable {s κ : ℕ} (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t]

end Main

section Final
variable {s κ : ℕ} (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t]

end Final

end GlobalTheory.SymChain.NonZeroAt

namespace GlobalTheory.SymChain

end GlobalTheory.SymChain
