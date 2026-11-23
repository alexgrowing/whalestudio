import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.MapPhiOfModM

noncomputable section

namespace PI.VolSemiDirect.W.Cj

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Measure
open scoped NNReal

section Gen

variable {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [LocallyCompactSpace A] [SecondCountableTopology A] [T2Space A] [MeasurableSpace A]
  [BorelSpace A] {k : ℕ}

def trG (X : GL (Fin k) A) : GL (Fin k) A where
  val := (X : Matrix (Fin k) (Fin k) A).transpose
  inv := ((X⁻¹ : GL (Fin k) A) : Matrix (Fin k) (Fin k) A).transpose
  val_inv := by
    rw [← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.transpose_one]
  inv_val := by
    rw [← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.transpose_one]

theorem trG_val (X : GL (Fin k) A) :
    ((trG X : GL (Fin k) A) : Matrix (Fin k) (Fin k) A) = (X : Matrix (Fin k) (Fin k) A).transpose :=
  rfl

theorem trG_mul (X Y : GL (Fin k) A) : trG (X * Y) = trG Y * trG X := by
  ext1
  simp [trG_val, Matrix.transpose_mul]

theorem trG_one : trG (1 : GL (Fin k) A) = 1 := by
  ext1
  simp [trG_val]

theorem trG_inv (X : GL (Fin k) A) : trG X⁻¹ = (trG X)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← trG_mul, mul_inv_cancel, trG_one]

theorem modM_transv (hT : TransvHaar) (X : GL (Fin k) A) (i j : Fin k) (hij : i ≠ j) (c : A)
    (hX : (X : Matrix (Fin k) (Fin k) A) = Matrix.transvection i j c) : modM X = 1 := by
  have h := hT A k i j hij c (addHaar : Measure (Fin k → A)) inferInstance
  have e : (phi X : (Fin k → A) → (Fin k → A)) = Matrix.mulVec (Matrix.transvection i j c) := by
    funext v
    rw [phi_apply, hX]
  apply modM_of_map X (addHaar : Measure (Fin k → A))
  rw [e]
  exact h

theorem transvection_transpose (i j : Fin k) (c : A) :
    (Matrix.transvection i j c).transpose = Matrix.transvection j i c := by
  ext a b
  simp [Matrix.transvection, Matrix.transpose_apply, Matrix.one_apply, Matrix.single_apply]
  aesop

theorem modM_tr_of_mem (hT : TransvHaar) (X : GL (Fin k) A)
    (hX : X ∈ Subgroup.closure ({g : GL (Fin k) A | ∃ i j c, i ≠ j ∧
      (g : Matrix (Fin k) (Fin k) A) = Matrix.transvection i j c} ∪
      {g | ∃ d : Fin k → A, (g : Matrix (Fin k) (Fin k) A) = Matrix.diagonal d})) :
    modM (trG X) = modM X := by
  induction hX using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with ⟨i, j, c, hij, hx⟩ | ⟨d, hx⟩
    · rw [modM_transv hT x i j hij c hx, modM_transv hT (trG x) j i hij.symm c
        (by rw [trG_val, hx, transvection_transpose])]
    · have : trG x = x := by
        ext1
        rw [trG_val, hx, Matrix.diagonal_transpose]
      rw [this]
  | one => rw [trG_one]
  | mul x y _ _ hx hy => rw [trG_mul, modM_mul, modM_mul, hx, hy, mul_comm]
  | inv x _ hx => rw [trG_inv, modM_inv, modM_inv, hx]

end Gen

theorem nnreal_eq_one_of_mul_self {x : ℝ≥0} (h : x * x = 1) : x = 1 := by
  have h' : (x : ℝ) * x = 1 := by exact_mod_cast h
  have : (x : ℝ) = 1 := by nlinarith [x.coe_nonneg]
  exact_mod_cast this

theorem orthInv_of (h1 : AdeleStableRankOne) (h2 : ElimSR1) (h3 : TransvHaar) : OrthInv := by
  intro F _ _ k G X hG hXG μ hμ
  obtain ⟨hlc, hsc, ht2⟩ := PI.VolStabSW.TopoAF.afTop_holds F
  have : BorelSpace (AF F) := ⟨rfl⟩
  have hd := congrArg Matrix.det hXG
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at hd
  have hdd : X.det * X.det = 1 := by
    have : (X.det * X.det) * G.det = 1 * G.det := by
      calc (X.det * X.det) * G.det = X.det * G.det * X.det := by ring
        _ = 1 * G.det := by rw [hd, one_mul]
    exact hG.mul_left_inj.1 this
  have hX : IsUnit X.det := ⟨⟨X.det, X.det, hdd, hdd⟩, rfl⟩
  let Xu : GL (Fin k) (AF F) := Matrix.nonsingInvUnit X hX
  let Gu : GL (Fin k) (AF F) := Matrix.nonsingInvUnit G hG
  have hrel : trG Xu * Gu * Xu = Gu := by
    ext1
    exact hXG
  have hm := congrArg modM hrel
  rw [modM_mul, modM_mul, modM_tr_of_mem h3 Xu (h2 (AF F) (h1 F) k Xu)] at hm
  have hpos : 0 < modM Gu := addEquivAddHaarChar_pos (phi Gu)
  have hsq : modM Xu * modM Xu = 1 := by
    have : (modM Xu * modM Xu) * modM Gu = 1 * modM Gu := by
      calc (modM Xu * modM Xu) * modM Gu = modM Xu * modM Gu * modM Xu := by ring
        _ = 1 * modM Gu := by rw [hm, one_mul]
    exact mul_right_cancel₀ hpos.ne' this
  have hmod := nnreal_eq_one_of_mul_self hsq
  have e := map_phi_of_modM Xu hmod μ
  have e2 : (phi Xu : (Fin k → AF F) → (Fin k → AF F)) = Matrix.mulVec X := by
    funext v
    rfl
  rw [e2] at e
  exact e

end PI.VolSemiDirect.W.Cj
