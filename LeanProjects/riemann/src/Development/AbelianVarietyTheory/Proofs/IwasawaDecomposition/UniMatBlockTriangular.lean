import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsClosedFlagsIff

set_option autoImplicit false

noncomputable section

open Module TopologicalSpace

namespace GlobalTheory.FlagPts

def AffPts (k J : Type) : Type := J → k

instance instTopAffPts (k J : Type) [Field k] : TopologicalSpace (AffPts k J) :=
  .generateFrom {s | ∃ p : MvPolynomial J k, s = {x | MvPolynomial.eval x p ≠ 0}}

instance (k J : Type) [Field k] : Zero (AffPts k J) := ⟨fun _ => 0⟩

theorem isOpen_affPts_ne_zero {k J : Type} [Field k] (p : MvPolynomial J k) :
    IsOpen {x : AffPts k J | MvPolynomial.eval x p ≠ 0} :=
  isOpen_generateFrom_of_mem ⟨p, rfl⟩

variable (k : Type) [Field k] {ι : Type} (V : ι → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]

def CellIdx : Type := Σ i : ι, {p : Fin (finrank k (V i)) × Fin (finrank k (V i)) // p.2 < p.1}

instance [Fintype ι] : Fintype (CellIdx k V) := by
  unfold CellIdx
  infer_instance

variable {k V}

def uniMat (u : AffPts k (CellIdx k V)) (i : ι) : Matrix (Fin (finrank k (V i))) (Fin (finrank k (V i))) k :=
  fun a c => if a = c then 1 else if h : c < a then u ⟨i, (a, c), h⟩ else 0

theorem uniMat_apply_self (u : AffPts k (CellIdx k V)) (i : ι) (a : Fin (finrank k (V i))) : uniMat u i a a = 1 := by
  simp [uniMat]

theorem uniMat_apply_of_lt (u : AffPts k (CellIdx k V)) (i : ι) {a c : Fin (finrank k (V i))} (h : c < a) :
    uniMat u i a c = u ⟨i, (a, c), h⟩ := by
  simp [uniMat, h, h.ne']

theorem uniMat_apply_of_gt (u : AffPts k (CellIdx k V)) (i : ι) {a c : Fin (finrank k (V i))} (h : a < c) :
    uniMat u i a c = 0 := by
  simp [uniMat, h.ne, not_lt.2 h.le]

theorem uniMat_blockTriangular (u : AffPts k (CellIdx k V)) (i : ι) : (uniMat u i).BlockTriangular OrderDual.toDual :=
  fun a c h => uniMat_apply_of_gt u i (by simpa using h)

theorem det_uniMat (u : AffPts k (CellIdx k V)) (i : ι) : (uniMat u i).det = 1 := by
  rw [Matrix.det_of_lowerTriangular _ (uniMat_blockTriangular u i)]
  simp [uniMat_apply_self]

def cellFrame (b : Frames k V) (u : AffPts k (CellIdx k V)) : Frames k V := fun i =>
  (b i).map (Matrix.toLinearEquiv (b i) (uniMat u i) (by rw [det_uniMat]; exact isUnit_one))

theorem cellFrame_apply (b : Frames k V) (u : AffPts k (CellIdx k V)) (i : ι) (c : Fin (finrank k (V i))) :
    cellFrame b u i c = ∑ a, uniMat u i a c • b i a := by
  simp [cellFrame, Matrix.toLin_self]

def cellMap (b : Frames k V) (u : AffPts k (CellIdx k V)) : Flags k V := (cellFrame b u).flags

theorem uniMat_zero (i : ι) : uniMat (0 : AffPts k (CellIdx k V)) i = 1 := by
  ext a c
  by_cases h : a = c
  · subst h; simp [uniMat_apply_self]
  · rw [Matrix.one_apply_ne h]
    simp only [uniMat, h, if_false]
    split_ifs <;> rfl

theorem cellFrame_zero (b : Frames k V) : cellFrame b 0 = b := by
  funext i
  ext c
  rw [cellFrame_apply, uniMat_zero]
  simp [Matrix.one_apply]

theorem cellMap_zero (b : Frames k V) : cellMap b 0 = b.flags := by
  rw [cellMap, cellFrame_zero]

end GlobalTheory.FlagPts
