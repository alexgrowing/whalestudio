import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.HermitianMatrixIdentities
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.ModelSecond

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants
open scoped ENNReal

namespace Formalism.L2.SG.monomialWeightModel

open Formalism.MainNotions.BigCellDensity Formalism.FourierDecayAlt.P.Dx2.Rad

variable {r : ℕ} (pN : Formalism.MainNotions.S.Point ℂ (r + 1))

local notation "W" => wPt pN

theorem w_symm (x : Fin (r + 1)) : (W).symm x = W x := (Equiv.symm_apply_eq _).2 (wPt_invol pN x).symm

def sw (q : Formalism.FourierDecayAlt.C2.Lstidx W) : Formalism.FourierDecayAlt.C2.Lstidx W :=
  ⟨(W q.1.2, W q.1.1), by
    have h := q.2
    refine ⟨?_, ?_⟩
    · rw [← w_symm, ← w_symm]; exact h.2
    · rw [w_symm, w_symm, wPt_invol, wPt_invol]; exact h.1⟩

theorem sw_sw (q : Formalism.FourierDecayAlt.C2.Lstidx W) : sw pN (sw pN q) = q := by
  apply Subtype.ext
  exact Prod.ext (wPt_invol pN _) (wPt_invol pN _)

def swE : Formalism.FourierDecayAlt.C2.Lstidx W ≃ Formalism.FourierDecayAlt.C2.Lstidx W where
  toFun := sw pN
  invFun := sw pN
  left_inv := sw_sw pN
  right_inv := sw_sw pN

variable (d : Fin (r + 1) → ℂ)

def Rm (x' : Formalism.FourierDecayAlt.C2.Lstidx W → ℂ) : Formalism.FourierDecayAlt.C2.Lstidx W → ℂ :=
  fun q => d (W q.1.1) / d (W q.1.2) * star (x' (sw pN q))

private theorem low_apply' (v : Formalism.FourierDecayAlt.C2.Lstidx W → ℂ) (i j : Fin (r + 1)) :
    low W v i j = (if i = j then 1 else 0) +
      (if h : j < i ∧ (W).symm i < (W).symm j then v ⟨(i, j), h⟩ else 0) := by
  simp only [Formalism.FourierDecayAlt.P.Dx2.Rad.low, Formalism.FourierDecayAlt.C2.lowOf, Matrix.add_apply, Matrix.one_apply, Matrix.of_apply]
  congr 1
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨(i, j), h⟩]
    · simp
    · intro q _ hq
      rw [if_neg]
      intro hq'
      exact hq (Subtype.ext hq')
    · intro hh
      exact absurd (Finset.mem_univ _) hh
  · refine Finset.sum_eq_zero fun q _ => ?_
    rw [if_neg]
    intro hq'
    apply h
    have hq2 := q.2
    rw [hq'] at hq2
    exact hq2

theorem low_R_mono (hd : ∀ a, d a ≠ 0) (x' : Formalism.FourierDecayAlt.C2.Lstidx W → ℂ) :
    low W (Rm pN d x') * Formalism.FourierDecayAlt.C2.monoP W d = Formalism.FourierDecayAlt.C2.monoP W d * (low W x')ᴴ := by
  ext i b
  rw [Matrix.mul_apply, Matrix.mul_apply,
    Finset.sum_eq_single ((wPt pN) b) (fun c _ hc => by simp [Formalism.FourierDecayAlt.C2.monoP, hc]) (by simp),
    Finset.sum_eq_single ((wPt pN) i) (fun a _ ha => by
      have hia : i ≠ (wPt pN) a := fun hi => ha (by rw [hi, wPt_invol])
      simp [Formalism.FourierDecayAlt.C2.monoP, hia]) (by simp)]
  simp only [Formalism.FourierDecayAlt.C2.monoP, Matrix.of_apply, Matrix.conjTranspose_apply, wPt_invol, eq_self_iff_true,
    if_true]
  rw [low_apply', low_apply']
  by_cases h1 : i = (wPt pN) b
  · subst h1
    simp [wPt_invol, w_symm]
  · have h1' : b ≠ (wPt pN) i := fun h => h1 (by rw [h, wPt_invol])
    rw [if_neg h1, if_neg h1', zero_add, zero_add]
    have key : ((wPt pN) b < i ∧ (wPt pN).symm i < (wPt pN).symm ((wPt pN) b)) ↔
        ((wPt pN) i < b ∧ (wPt pN).symm b < (wPt pN).symm ((wPt pN) i)) := by
      rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply, w_symm, w_symm]
      exact And.comm
    by_cases h2 : (wPt pN) b < i ∧ (wPt pN).symm i < (wPt pN).symm ((wPt pN) b)
    · have h3 := key.1 h2
      have hsw : sw pN ⟨(i, (wPt pN) b), h2⟩ = ⟨(b, (wPt pN) i), h3⟩ :=
        Subtype.ext (Prod.ext (wPt_invol pN b) rfl)
      rw [dif_pos h2, dif_pos h3]
      simp only [Rm]
      rw [hsw, wPt_invol]
      field_simp [hd b]
    · have h3 : ¬ ((wPt pN) i < b ∧ (wPt pN).symm b < (wPt pN).symm ((wPt pN) i)) := fun h => h2 (key.2 h)
      rw [dif_neg h2, dif_neg h3]
      simp

theorem mono_mul_inv (hd : ∀ a, d a ≠ 0) :
    Formalism.FourierDecayAlt.C2.monoP W d * Formalism.FourierDecayAlt.C2.monoP (wPt pN).symm (fun j => (d ((wPt pN).symm j))⁻¹) = 1 := by
  ext i b
  simp only [Formalism.FourierDecayAlt.C2.monoP, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single ((wPt pN).symm b)]
  · simp only [Equiv.apply_symm_apply, eq_self_iff_true, if_true]
    split_ifs with h
    · exact mul_inv_cancel₀ (hd _)
    · exact zero_mul _
  · intro a _ ha
    simp [ha]
  · intro h
    exact absurd (Finset.mem_univ _) h

end Formalism.L2.SG.monomialWeightModel

end
