import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

open Finset
open scoped ComplexConjugate Matrix

noncomputable section

theorem orderEmbOfFin_map_castLEEmb {l N : ℕ} (hl : l ≤ N)
    (h : ((univ : Finset (Fin l)).map (Fin.castLEEmb hl)).card = l) :
    (((univ : Finset (Fin l)).map (Fin.castLEEmb hl)).orderEmbOfFin h : Fin l → Fin N) =
      Fin.castLE hl := by
  symm
  apply Finset.orderEmbOfFin_unique
  · intro x
    exact Finset.mem_map.mpr ⟨x, mem_univ x, rfl⟩
  · intro a b hab
    exact hab

theorem sum_sq_norm_pluckerCoord_eq_det_mul_conjTranspose (h0 : PluckerFrameChange.Statement)
    {l N : ℕ} (V : Matrix (Fin l) (Fin N) ℂ) :
    (((∑ I ∈ powersetCard l (univ : Finset (Fin N)), ‖pluckerCoord V I‖ ^ 2 : ℝ)) : ℂ) =
      (V * Vᴴ).det := by
  by_cases hl : l ≤ N
  · let g : Matrix (Fin N) (Fin N) ℂ :=
      Matrix.of fun k j => if h : j.val < l then star (V ⟨j.val, h⟩ k) else 0
    let I0 : Finset (Fin N) := (univ : Finset (Fin l)).map (Fin.castLEEmb hl)
    have hI0 : I0.card = l := by simp [I0]
    have hemb := orderEmbOfFin_map_castLEEmb hl hI0
    have key := h0 ℂ l N V g I0 hI0
    have lhs : pluckerCoord (V * g) I0 = (V * Vᴴ).det := by
      unfold pluckerCoord
      rw [dif_pos hI0]
      congr 1
      ext i j
      simp [I0, Matrix.mul_apply, hemb, g, Matrix.conjTranspose_apply]
    have rhs : ∀ J ∈ powersetCard l (univ : Finset (Fin N)),
        pluckerCoord V J * minorOn g l J I0 = ((‖pluckerCoord V J‖ ^ 2 : ℝ) : ℂ) := by
      intro J hJ
      have hJc : J.card = l := (mem_powersetCard.mp hJ).2
      have hm : minorOn g l J I0 = star (pluckerCoord V J) := by
        unfold minorOn pluckerCoord
        rw [dif_pos ⟨hJc, hI0⟩, dif_pos hJc, ← Matrix.det_conjTranspose]
        congr 1
        ext i j
        simp [I0, hemb, g, Matrix.conjTranspose_apply]
      rw [hm, Complex.star_def, RCLike.mul_conj]
      push_cast
      rfl
    rw [← lhs, key, Complex.ofReal_sum]
    exact (sum_congr rfl rhs).symm
  · rw [not_le] at hl
    have hE : powersetCard l (univ : Finset (Fin N)) = ∅ :=
      Finset.powersetCard_eq_empty.mpr (by simpa using hl)
    rw [hE, sum_empty, Complex.ofReal_zero, eq_comm]
    by_contra hd
    have hu : IsUnit (V * Vᴴ) := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hd)
    have h1 := Matrix.rank_of_isUnit _ hu
    have h2 := (Matrix.rank_mul_le_left V Vᴴ).trans (Matrix.rank_le_width V)
    simp only [Fintype.card_fin] at h1
    omega

theorem GramSumOfMinors.proof (h0 : PluckerFrameChange.Statement) : GramSumOfMinors.Statement := by
  intro l N V
  have hg := sum_sq_norm_pluckerCoord_eq_det_mul_conjTranspose h0 V
  refine ⟨hg, fun hd => ?_⟩
  have hS : (0 : ℝ) ≤ ∑ I ∈ powersetCard l (univ : Finset (Fin N)), ‖pluckerCoord V I‖ ^ 2 :=
    sum_nonneg fun _ _ => by positivity
  rw [← Finset.sum_div, ← hg, Complex.norm_real, Real.norm_of_nonneg hS]
  apply div_self
  intro hz
  apply hd
  rw [← hg, hz, Complex.ofReal_zero]

end

end GroundTheory.Heights₂.Heights.FlagBundles
