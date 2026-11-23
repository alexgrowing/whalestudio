import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainOnto.RightMove

variable {D : D7}

theorem topL_mul {κ : Type} [CommRing κ] {a b : ℕ} (y : Matrix (Fin b) (Fin a) κ) (γ : Matrix (Fin a) (Fin a) κ) :
    topL a (y * γ) = topL a y * γ := by
  ext i j
  by_cases hi : i.val < b
  · simp [topL, Matrix.mul_apply, hi]
  · simp [topL, Matrix.mul_apply, hi]

theorem lowZero_mul {κ : Type} [CommRing κ] {a b : ℕ} {y : Matrix (Fin b) (Fin a) κ} (hy : LowZero a y)
    (γ : Matrix (Fin a) (Fin a) κ) : LowZero a (y * γ) := by
  intro i j hi _
  rw [Matrix.mul_apply]
  exact Finset.sum_eq_zero fun l _ => by rw [hy i l hi l.2, zero_mul]

abbrev Cond {a b : ℕ} (L : LevDat D.host.E ℂ a) (y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP)) : Prop :=
  (∀ PP ∈ L.Pg, LowZero a (y PP)) ∧ ∃ g : ∀ PP : ↥L.Pg, GL (Fin a) (kP PP.1),
    (∀ PP : ↥L.Pg, ((g PP : GL (Fin a) _) : Matrix (Fin a) (Fin a) _) = topL a (y PP.1)) ∧
    (∀ PP : ↥L.Pg, g PP ∈ blockTri (blkOf L.r L.t)) ∧ (fun PP => upperLeftBlock L.hr (g PP)) ∈ L.P.H

theorem cond_mul {a b : ℕ} (L : LevDat D.host.E ℂ a) (γ : ∀ PP : Pl D.host.E, GL (Fin a) (kP PP))
    (hγ : ∀ PP ∈ L.Pg, γ PP ∈ blockTri (blkOf L.r L.t)) (hP : (fun PP : ↥L.Pg => upperLeftBlock L.hr (γ PP.1)) ∈ L.P.H)
    (y z : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP)) (hz : ∀ PP, z PP = y PP * (γ PP).val)
    (h : Cond L y) : Cond L z := by
  obtain ⟨h1, g, h2, h3, h4⟩ := h
  refine ⟨fun PP hP' => (hz PP).symm ▸ lowZero_mul (h1 PP hP') _, fun PP => g PP * γ PP.1, fun PP => ?_,
    fun PP => mul_mem (h3 PP) (hγ PP.1 PP.2), ?_⟩
  · rw [Units.val_mul, h2, hz, topL_mul]
  · have e : (fun PP : ↥L.Pg => upperLeftBlock L.hr (g PP * γ PP.1)) =
        (fun PP => upperLeftBlock L.hr (g PP)) * (fun PP : ↥L.Pg => upperLeftBlock L.hr (γ PP.1)) := by
      funext PP
      exact extendMatrixByIdentityAlongIndices_mul _ (blockTri_blkOf_le _ _ (h3 PP)) (blockTri_blkOf_le _ _ (hγ PP.1 PP.2))
    rw [e]
    exact mul_mem h4 hP

theorem omegaG_mul_right : ∀ (D : D7) (a b : ℕ) (L : LevDat D.host.E ℂ a) (χ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (G : ∀ PP : Pl D.host.E, GL (Fin a) (kP PP)), (∀ PP ∈ L.Pg, G PP ∈ blockTri (blkOf L.r L.t)) → ∀ hP : (fun PP : ↥L.Pg => upperLeftBlock L.hr (G PP.1)) ∈ L.P.H, ∀ y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP), omegaG L χ (fun PP => y PP * (G PP).val) = ((L.P.chi ⟨_, hP⟩ * (∏ PP ∈ L.Pg, ∏ i ∈ Finset.range L.s, L.cg (i + 1) PP (dBlk (blkOf L.r L.t) (i + 1) (G PP))) * ∏ PP ∈ L.Pg, (χ PP (Matrix.GeneralLinearGroup.det (G PP)))⁻¹ : ℂˣ) : ℂ) * omegaG L χ y := by
  intro D a b L χ G hG hP y
  have hGi : ∀ PP ∈ L.Pg, (G PP)⁻¹ ∈ blockTri (blkOf L.r L.t) := fun PP h => inv_mem (hG PP h)
  have hPi : (fun PP : ↥L.Pg => upperLeftBlock L.hr (G PP.1)⁻¹) ∈ L.P.H := by
    have e : (fun PP : ↥L.Pg => upperLeftBlock L.hr (G PP.1)⁻¹) = (fun PP : ↥L.Pg => upperLeftBlock L.hr (G PP.1))⁻¹ := by
      funext PP
      exact extendOne_inv _ (blockTri_blkOf_le _ _ (hG PP.1 PP.2))
    rw [e]
    exact inv_mem hP
  unfold omegaG
  by_cases hy : Cond L y
  · have hy' : Cond L (fun PP => y PP * (G PP).val) := cond_mul L G hG hP y _ (fun _ => rfl) hy
    rw [dif_pos hy', dif_pos hy]
    have key : ∀ PP : ↥L.Pg, hy'.2.choose PP = hy.2.choose PP * G PP.1 := fun PP => Units.ext (by
      rw [Units.val_mul, hy'.2.choose_spec.1 PP, hy.2.choose_spec.1 PP, topL_mul])
    have hc : (⟨fun PP => upperLeftBlock L.hr (hy'.2.choose PP), hy'.2.choose_spec.2.2⟩ : L.P.H) =
        ⟨fun PP => upperLeftBlock L.hr (hy.2.choose PP), hy.2.choose_spec.2.2⟩ * ⟨_, hP⟩ :=
      Subtype.ext (funext fun PP => by
        show upperLeftBlock L.hr (hy'.2.choose PP) = upperLeftBlock L.hr (hy.2.choose PP) * upperLeftBlock L.hr (G PP.1)
        rw [key]
        exact extendMatrixByIdentityAlongIndices_mul _ (blockTri_blkOf_le _ _ (hy.2.choose_spec.2.1 PP)) (blockTri_blkOf_le _ _ (hG PP.1 PP.2)))
    have hd : ∀ PP : ↥L.Pg, ∀ c : ℕ, dBlk (blkOf L.r L.t) c (hy'.2.choose PP) =
        dBlk (blkOf L.r L.t) c (hy.2.choose PP) * dBlk (blkOf L.r L.t) c (G PP.1) := fun PP c => by
      rw [key]; exact diag_block_det_mul (hy.2.choose_spec.2.1 PP) (hG PP.1 PP.2)
    rw [hc, map_mul]
    simp only [hd]
    simp only [key, map_mul, Units.val_mul, mul_inv, Finset.prod_mul_distrib, Units.val_inv_eq_inv_val, Units.coe_prod]
    rw [← Finset.prod_coe_sort L.Pg (fun PP => ((χ PP (Matrix.GeneralLinearGroup.det (G PP)) : ℂˣ) : ℂ)⁻¹),
      ← Finset.prod_coe_sort L.Pg (fun PP => ∏ i ∈ Finset.range L.s, ((L.cg (i + 1) PP (dBlk (blkOf L.r L.t) (i + 1) (G PP)) : ℂˣ) : ℂ))]
    ring
  · have hy' : ¬ Cond L (fun PP => y PP * (G PP).val) := fun h => hy (cond_mul L (fun PP => (G PP)⁻¹) hGi hPi _ y
      (fun PP => by rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]) h)
    rw [dif_neg hy', dif_neg hy, mul_zero]

end GlobalTheory.ChainOnto.RightMove
