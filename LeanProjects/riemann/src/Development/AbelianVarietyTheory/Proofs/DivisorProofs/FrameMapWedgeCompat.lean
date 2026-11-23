import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameAtApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarAddVectorScalar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtMapComp
open Matrix MeasureTheory Set Filter Topology GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.Gauge
open scoped ContDiff

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TorsionForm.FrameWedge

theorem fibMat_row_castAdd (n : ℕ) {g : ℕ} (a : Matrix (Fin g) (Fin g) ℂ) (k : Fin (n + n)) :
    fibMat n a (Fin.castAdd g k) = Pi.single (Fin.castAdd g k) 1 := by
  funext j
  refine Fin.addCases (fun j' => ?_) (fun j' => ?_) j
  · simp [fibMat, Pi.single_apply, Matrix.one_apply, eq_comm]
  · have h : Fin.natAdd (n + n) j' ≠ Fin.castAdd g k := by
      intro h; have := congrArg Fin.val h; simp at this; omega
    simp [fibMat, Pi.single_apply, h]

theorem fibMat_row_natAdd (n : ℕ) {g : ℕ} (a : Matrix (Fin g) (Fin g) ℂ) (c : Fin g) (j : Fin g) :
    fibMat n a (Fin.natAdd (n + n) c) (Fin.natAdd (n + n) j) = a c j := by
  simp [fibMat]

theorem fibMat_row_natAdd_castAdd (n : ℕ) {g : ℕ} (a : Matrix (Fin g) (Fin g) ℂ) (c : Fin g)
    (j : Fin (n + n)) : fibMat n a (Fin.natAdd (n + n) c) (Fin.castAdd g j) = 0 := by
  simp [fibMat]

theorem frameMap_wedge_castAdd {g : ℕ} (n : ℕ) (D : Matrix (Fin g) (Fin g) ℂ) (k : Fin (n + n))
    (w : Ext (n + n + g)) :
    frameMap n D (wedge (Fin.castAdd g k) w) = wedge (Fin.castAdd g k) (frameMap n D w) := by
  unfold frameMap
  rw [GlobalTheory.ExtFunctor.extMap_wedge, GlobalTheory.ExtFunctor.wedgeVec_apply, fibMat_row_castAdd,
    Finset.sum_eq_single (Fin.castAdd g k)]
  · simp
  · intro b _ hb; simp [Pi.single_apply, hb]
  · simp

theorem frameMap_wedge : ∀ {g : ℕ} (n : ℕ) (D : Matrix (Fin g) (Fin g) ℂ) (w : Ext (n + n + g)),
    (∀ c : Fin g, frameMap n D (wedge (dzb n c) w) = ∑ a, star (D⁻¹ a c) • wedge (dzb n a) (frameMap n D w)) ∧
    ∀ i : Fin n, frameMap n D (wedge (dt g i) w) = wedge (dt g i) (frameMap n D w) ∧
      frameMap n D (wedge (dtb g i) w) = wedge (dtb g i) (frameMap n D w) := by
  intro g n D w
  refine ⟨fun c => ?_, fun i => ⟨frameMap_wedge_castAdd n D _ w, frameMap_wedge_castAdd n D _ w⟩⟩
  have e : frameMap n D (wedge (dzb n c) w) =
      GlobalTheory.ExtFunctor.wedgeVec (fibMat n (D⁻¹)ᴴ (dzb n c)) (frameMap n D w) :=
    GlobalTheory.ExtFunctor.extMap_wedge _ _ _
  rw [e, GlobalTheory.ExtFunctor.wedgeVec_apply, Fin.sum_univ_add]
  simp only [dzb, fibMat_row_natAdd_castAdd, fibMat_row_natAdd, zero_smul, Finset.sum_const_zero,
    zero_add, Matrix.conjTranspose_apply]

end GlobalTheory.TorsionForm.FrameWedge
