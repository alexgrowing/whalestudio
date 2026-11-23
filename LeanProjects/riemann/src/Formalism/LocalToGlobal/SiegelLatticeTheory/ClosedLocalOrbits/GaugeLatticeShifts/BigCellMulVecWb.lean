import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.HaarOnSkOfB
import Formalism.FormalDegreeBessel.FinalBF
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TwoByOneBlock

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal ComplexConjugate
open Matrix

namespace Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting

theorem bigMem_holds : BigMem := Formalism.QuantumDeterminants.bigCellMem

theorem hJ_P {n : ℕ} {ε : Fin n → Bool} {P H : Matrix (Fin n) (Fin n) ℂ} (hPJ : Pᴴ * Formalism.REAL.Jm ε * P = H)
    (x y : Fin n → ℂ) : hJ ε (P *ᵥ x) (P *ᵥ y) = Formalism.QuantumDeterminants.herm H y x := by
  unfold hJ Formalism.QuantumDeterminants.herm
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hPJ]

theorem hJ_smul_l {n : ℕ} (ε : Fin n → Bool) (a : ℂ) (x y : Fin n → ℂ) : hJ ε (a • x) y = conj a * hJ ε x y := by
  unfold hJ
  rw [star_smul, smul_dotProduct, smul_eq_mul, Complex.star_def]

theorem hJ_smul_r {n : ℕ} (ε : Fin n → Bool) (a : ℂ) (x y : Fin n → ℂ) : hJ ε x (a • y) = a * hJ ε x y := by
  unfold hJ
  rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem fam_eq {r k : ℕ} {P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    {e : Fin r → Fin (2 * r + k + 1) → ℂ} {z zH : Fin (2 * r + k + 1) → ℂ}
    (hPe : ∀ a, P *ᵥ Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI k r a) = e a) (hPz : P *ᵥ zH = z) (a : Fin (r + 1)) :
    fam e z a = P *ᵥ Formalism.QuantumDeterminants.fvec k r zH a := by
  unfold fam Formalism.QuantumDeterminants.fvec
  split_ifs with h
  · have ha : a = Fin.castSucc ⟨a.val, h⟩ := Fin.ext rfl
    conv_lhs => rw [ha]
    rw [Fin.snoc_castSucc]
    exact (hPe _).symm
  · have ha : a = Fin.last r := Fin.ext (by have := a.2; simp only [Fin.val_last]; omega)
    subst ha
    rw [Fin.snoc_last]
    exact hPz.symm

theorem bigCell_mulVec_wb {k r : ℕ} (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    {w : Fin (2 * r + k + 1) → ℂ} (hw : Formalism.QuantumDeterminants.inWb k r w) :
    Formalism.QuantumDeterminants.bigCell k r c μ *ᵥ w = Formalism.FourierDecayAlt.B2.embWb k r μ *ᵥ w := by
  ext i
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : r ≤ j.val ∧ j.val ≤ r + k
  · have hj1 : ¬ j.val < r := by omega
    unfold Formalism.QuantumDeterminants.bigCell Formalism.FourierDecayAlt.B2.embWb
    rw [dif_neg hj1, dif_pos hj.2]
    by_cases hi : r ≤ i.val ∧ i.val ≤ r + k
    · rw [dif_pos hi, dif_pos ⟨hi, hj⟩]
    · rw [dif_neg hi, dif_neg (fun h => hi h.1),
        if_neg (fun (h : i = j ∧ ¬(r ≤ i.val ∧ i.val ≤ r + k)) => hi (by rw [h.1]; exact hj))]
  · rw [hw j (by omega)]
    simp

theorem conj_scinv (sc : ℝ) (m : ℕ) : conj (((sc : ℂ) ^ m)⁻¹) = ((sc : ℂ) ^ m)⁻¹ := by
  simp [map_inv₀, map_pow]

theorem zBig : ZBig := by
  intro r k ε e z z' zH zH' P sc hPJ hPdet hPe hzH hzH' hPz hPz' hsc μsec hsec q hq hζ
  have hU : (μsec q.2)ᴴ * Formalism.QuantumDeterminants.Hb k * μsec q.2 = Formalism.QuantumDeterminants.Hb k := (hsec.2 q.2 hζ).1
  refine ⟨inUJ_conj hPJ hPdet (bigMem_holds k r q.1 _ hq hU), ?_⟩
  have h2 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hPdet
  have hB : ∀ y, (P * Formalism.QuantumDeterminants.bigCell k r q.1 (μsec q.2) * P⁻¹) *ᵥ (P *ᵥ y) =
      P *ᵥ (Formalism.QuantumDeterminants.bigCell k r q.1 (μsec q.2) *ᵥ y) := by
    intro y
    rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, h2, Matrix.mul_one, ← Matrix.mulVec_mulVec]
  have hlast : Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) (Formalism.QuantumDeterminants.bigCell k r q.1 (μsec q.2) *ᵥ zH') zH = q.2 := by
    have h1W : (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) ∈ Formalism.QuantumDeterminants.UWset k r zH := by
      refine ⟨by simp [Formalism.QuantumDeterminants.UH], fun a => by simp, by simp⟩
    have h1W' : (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) ∈ Formalism.QuantumDeterminants.UWset k r zH' := by
      refine ⟨by simp [Formalism.QuantumDeterminants.UH], fun a => by simp, by simp⟩
    have := (Formalism.FourierDecayAlt.P.b2_rank_one_mem k r zH zH' μsec hzH hzH' hsec q.2 hζ 1 h1W 1 h1W').2
    rw [inv_one, Matrix.one_mul, Matrix.mul_one] at this
    rw [bigCell_mulVec_wb q.1 _ hzH']
    exact this
  have hZ := Formalism.QuantumDeterminants.bigCellZhat k r zH zH' q.1 (μsec q.2) hzH hzH'
  ext a b
  simp only [Zhat, famSc]
  rw [Matrix.mulVec_smul, hJ_smul_l, hJ_smul_r, fam_eq hPe hPz a, fam_eq hPe hPz' b, hB, hJ_P hPJ]
  have hZab := congrFun (congrFun hZ a) b
  simp only [Formalism.QuantumDeterminants.Zhat] at hZab
  rw [hZab, conj_scinv]
  by_cases hab : a = b
  · subst hab
    rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
    by_cases ha : a.val < r
    · rw [dif_pos ha]
      have ha' : a = Fin.castSucc ⟨a.val, ha⟩ := Fin.ext rfl
      conv_rhs => rw [ha']
      unfold coordSc
      rw [Fin.snoc_castSucc]
      ring
    · rw [dif_neg ha, hlast]
      have ha' : a = Fin.last r := Fin.ext (by have := a.2; simp only [Fin.val_last]; omega)
      subst ha'
      unfold coordSc
      rw [Fin.snoc_last]
      simp
  · rw [Matrix.diagonal_apply_ne _ hab, Matrix.diagonal_apply_ne _ hab]
    ring

end Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL
