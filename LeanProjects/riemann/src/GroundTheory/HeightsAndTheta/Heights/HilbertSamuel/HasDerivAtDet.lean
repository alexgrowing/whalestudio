import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsLattice
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StandardLatticeVecIndep
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open Matrix Equiv
open scoped ComplexOrder

noncomputable section

theorem LogDetDerivative.hasDerivAt_det {m : ℕ} {G : ℝ → Matrix (Fin m) (Fin m) ℂ}
    {G' : Matrix (Fin m) (Fin m) ℂ} {t : ℝ} (h : ∀ i j, HasDerivAt (fun s ↦ G s i j) (G' i j) t) :
    HasDerivAt (fun s ↦ (G s).det) (∑ i, (G t).cramer (fun k ↦ G' k i) i) t := by
  have key : ∀ σ : Perm (Fin m), HasDerivAt (fun s ↦ ((Perm.sign σ : ℤ) : ℂ) * ∏ i, G s (σ i) i)
      (((Perm.sign σ : ℤ) : ℂ) * ∑ i, (∏ j ∈ Finset.univ.erase i, G t (σ j) j) * G' (σ i) i) t := by
    intro σ
    have := HasDerivAt.fun_finsetProd (u := Finset.univ) (f := fun i s ↦ G s (σ i) i)
      (f' := fun i ↦ G' (σ i) i) (x := t) (fun i _ ↦ h (σ i) i)
    simpa [smul_eq_mul] using this.const_mul ((Perm.sign σ : ℤ) : ℂ)
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun σ _ ↦ key σ)
  have hfun : (fun s ↦ (G s).det) =
      fun s ↦ ∑ σ : Perm (Fin m), ((Perm.sign σ : ℤ) : ℂ) * ∏ i, G s (σ i) i := by
    ext s
    exact det_apply' _
  rw [hfun]
  refine hsum.congr_deriv ?_
  symm
  rw [Finset.sum_congr rfl fun i _ ↦ cramer_apply (G t) (fun k ↦ G' k i) i]
  simp only [det_apply', Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ ↦ Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  have hrest : ∏ j ∈ Finset.univ.erase i, (G t).updateCol i (fun k ↦ G' k i) (σ j) j =
      ∏ j ∈ Finset.univ.erase i, G t (σ j) j := by
    refine Finset.prod_congr rfl fun j hj ↦ ?_
    rw [updateCol_ne (Finset.ne_of_mem_erase hj)]
  rw [hrest, updateCol_self]
  ring

theorem LogDetDerivative.sum_cramer_eq {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℂ)
    (hA : IsUnit A.det) :
    ∑ i, A.cramer (fun k ↦ B k i) i = A.det * (A⁻¹ * B).trace := by
  simp only [← det_smul_inv_mulVec_eq_cramer A _ hA, Pi.smul_apply, smul_eq_mul, trace,
    diag_apply, mul_apply, mulVec, dotProduct, Finset.mul_sum]

theorem LogDetDerivative.intersectionNumber_baseChange : LogDetDerivative.Statement := by
  intro m G G' hpos hG t
  have hdet := LogDetDerivative.hasDerivAt_det (hG t)
  rw [LogDetDerivative.sum_cramer_eq _ _ (hpos t).det_pos.ne'.isUnit] at hdet
  have hre : HasDerivAt (fun s ↦ (G s).det.re)
      ((G t).det * ((G t)⁻¹ * G' t).trace).re t := by
    exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hdet
  have hp := (hpos t).det_pos
  rw [Complex.lt_def] at hp
  obtain ⟨hre0, him0⟩ := hp
  simp only [Complex.zero_re, Complex.zero_im] at hre0 him0
  have hlog := (hre.log hre0.ne').const_mul (-(1 / 2) : ℝ)
  refine hlog.congr_deriv ?_
  rw [Complex.mul_re, ← him0, zero_mul, sub_zero]
  field_simp

theorem LogDetDerivative.equiv :
    GroundTheory.Heights₂.Heights.HilbertSamuel.LogDetDerivative.Statement ↔
      GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel.LogDetDerivative.Statement := by
  constructor
  · intro h m F t
    refine h m F.G (GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel.entryDeriv F.G) F.posDef
      (fun s i j ↦ ?_) t
    have hd := ((F.smooth i j).differentiable (by norm_num) s).hasDerivAt
    simpa [GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel.entryDeriv] using hd
  · intro _
    exact LogDetDerivative.intersectionNumber_baseChange

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
