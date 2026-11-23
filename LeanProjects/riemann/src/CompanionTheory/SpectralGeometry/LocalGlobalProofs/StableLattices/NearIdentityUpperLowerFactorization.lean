import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.EntryMulSubOne
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FactorizationBis

noncomputable section

open Matrix

namespace GlobalTheory.CompanionTheory.CartGL.IwahoriLU

variable {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L] {n : ℕ}

def blk (P : Matrix (Fin n) (Fin n) L) (b c : Fin n → L) (d : L) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) L :=
  fun i j => Fin.lastCases (motive := fun _ => L)
    (Fin.lastCases (motive := fun _ => L) d c j)
    (fun i' => Fin.lastCases (motive := fun _ => L) (b i') (P i') j) i

omit [IsUltrametricDist L] in
@[simp] theorem blk_cc (P : Matrix (Fin n) (Fin n) L) (b c : Fin n → L) (d : L) (i j : Fin n) :
    blk P b c d i.castSucc j.castSucc = P i j := by simp [blk]

omit [IsUltrametricDist L] in
@[simp] theorem blk_cl (P : Matrix (Fin n) (Fin n) L) (b c : Fin n → L) (d : L) (i : Fin n) :
    blk P b c d i.castSucc (Fin.last n) = b i := by simp [blk]

omit [IsUltrametricDist L] in
@[simp] theorem blk_lc (P : Matrix (Fin n) (Fin n) L) (b c : Fin n → L) (d : L) (j : Fin n) :
    blk P b c d (Fin.last n) j.castSucc = c j := by simp [blk]

omit [IsUltrametricDist L] in
@[simp] theorem blk_ll (P : Matrix (Fin n) (Fin n) L) (b c : Fin n → L) (d : L) :
    blk P b c d (Fin.last n) (Fin.last n) = d := by simp [blk]

theorem factor (n : ℕ) (r : ℝ) (h0 : 0 ≤ r) (h1 : r < 1) :
    ∀ A : Matrix (Fin n) (Fin n) L, (∀ i j, ‖(A - 1) i j‖ ≤ r) →
      ∃ U W : Matrix (Fin n) (Fin n) L, (∀ i j, j < i → U i j = 0) ∧ (∀ i j, i < j → W i j = 0) ∧
        (∀ i j, ‖(U - 1) i j‖ ≤ r) ∧ (∀ i j, ‖(W - 1) i j‖ ≤ r) ∧ A = U * W :=
  _root_.UpperTheory.Reformulated.B.TriangularFactorizationNearIdentity.factor n r h0 h1

theorem iwahori_factorisation (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] (n : ℕ) (r : ℝ)
    (h0 : 0 ≤ r) (h1 : r < 1) (A : Matrix (Fin n) (Fin n) L) (hA : ∀ i j, ‖(A - 1) i j‖ ≤ r) :
    ∃ U W : Matrix (Fin n) (Fin n) L, (∀ i j, j < i → U i j = 0) ∧ (∀ i j, i < j → W i j = 0) ∧
      (∀ i j, ‖(U - 1) i j‖ ≤ r) ∧ (∀ i j, ‖(W - 1) i j‖ ≤ r) ∧ A = U * W :=
  factor n r h0 h1 A hA

end GlobalTheory.CompanionTheory.CartGL.IwahoriLU
