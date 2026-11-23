import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OnMatInfOfIsUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecMatEqAdd
open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff

noncomputable section

namespace GlobalTheory.JSW.MirCinf

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem mapMatrix_secMatInf (ρ : Fin n) (j : InfinitePlace E → Fin n) (v : Fin n → Cinf E) (w : InfinitePlace E) :
    (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) w).mapMatrix (Matrix.of (secMatInf ρ j v)) =
      Matrix.of (secMat ρ (j w) (fun l => v l w)) := by
  ext i l; rfl

theorem isUnit_secMatInf (ρ : Fin n) (j : InfinitePlace E → Fin n) (hj : ∀ w, j w ≤ ρ) (v : Fin n → Cinf E)
    (hv : ∀ w, v (j w) w ≠ 0) : IsUnit (Matrix.of (secMatInf ρ j v)) := by
  rw [Matrix.isUnit_iff_isUnit_det, Pi.isUnit_iff]
  intro w
  have h := RingHom.map_det (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) w) (Matrix.of (secMatInf ρ j v))
  rw [mapMatrix_secMatInf] at h
  have hu := isUnit_secMat ρ (j w) (hj w) (fun l => v l w) (hv w)
  rw [Matrix.isUnit_iff_isUnit_det] at hu
  have h' : (Matrix.of (secMatInf ρ j v)).det w = (Matrix.of (secMat ρ (j w) (fun l => v l w))).det := h
  rw [h']
  exact hu

theorem secMatInf_mem_lev (ρ : Fin n) (j : InfinitePlace E → Fin n) (hj : ∀ w, j w ≤ ρ) (v : Fin n → Cinf E)
    (hv : ∀ w, v (j w) w ≠ 0) : toGLInf (Matrix.of (secMatInf ρ j v)) ∈ levSetInf E n (ρ + 1) := by
  rw [mem_levSetInf, val_toGLInf (isUnit_secMatInf ρ j hj v hv)]
  intro i hi
  have hiρ : ρ < i := by rw [Fin.lt_def]; omega
  refine ⟨fun l hl => funext fun w => ?_, funext fun w => ?_⟩
  · change secMat ρ (j w) (fun l => v l w) i l = 0
    rw [secMat_of_ne _ _ _ hiρ.ne', swap_of_lt' (hj w) hiρ, if_neg hl.ne]
  · change secMat ρ (j w) (fun l => v l w) i i = 1
    rw [secMat_of_ne _ _ _ hiρ.ne', swap_of_lt' (hj w) hiρ, if_pos rfl]

theorem rowCutInf_apply (ρ : Fin n) (g : GL (Fin n) (Cinf E)) (w : InfinitePlace E) (l : Fin n) :
    rowCutInf ρ (g : Matrix (Fin n) (Fin n) (Cinf E)) l w = rowCut ρ ((compGL w g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) l := by
  unfold rowCutInf rowCut
  split_ifs <;> rfl

def secLinInf (ρ : Fin n) : (Fin n → Cinf E) →L[ℝ] (Fin n → Fin n → Cinf E) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v i l => if i = ρ ∧ l ≤ ρ then v l else 0
      map_add' := fun v w => by
        funext i l
        by_cases h : i = ρ ∧ l ≤ ρ <;> simp [h]
      map_smul' := fun c v => by
        funext i l
        by_cases h : i = ρ ∧ l ≤ ρ <;> simp [h] }

theorem secMatInf_eq_add (ρ : Fin n) (j : InfinitePlace E → Fin n) (v : Fin n → Cinf E) :
    secMatInf ρ j v = secMatInf ρ j 0 + secLinInf ρ v := by
  funext i l w
  by_cases hi : i = ρ
  · subst hi
    by_cases hl : l ≤ i <;> simp [secMatInf, secMat, secLinInf, hl]
  · simp [secMatInf, secMat, secLinInf, hi]

theorem secMatInf_main : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (ρ : Fin n) (j : InfinitePlace E → Fin n), (∀ w, j w ≤ ρ) → (∀ v : Fin n → Cinf E, (∀ w, v (j w) w ≠ 0) → IsUnit (Matrix.of (secMatInf ρ j v)) ∧ toGLInf (Matrix.of (secMatInf ρ j v)) ∈ levSetInf E n (ρ + 1)) ∧ (∀ g ∈ levSetInf E n (ρ + 1), (∀ w, rowCutInf ρ (g : Matrix (Fin n) (Fin n) (Cinf E)) (j w) w ≠ 0) → g * (toGLInf (Matrix.of (secMatInf ρ j (rowCutInf ρ (g : Matrix (Fin n) (Fin n) (Cinf E))))))⁻¹ ∈ levSetInf E n ρ) ∧ ∃ L : (Fin n → Cinf E) →L[ℝ] (Fin n → Fin n → Cinf E), ∀ v, secMatInf ρ j v = secMatInf ρ j 0 + L v := by
  intro E _ _ n ρ j hj
  refine ⟨fun v hv => ⟨isUnit_secMatInf ρ j hj v hv, secMatInf_mem_lev ρ j hj v hv⟩, ?_, secLinInf ρ, secMatInf_eq_add ρ j⟩
  intro g hg hgj w
  set v := rowCutInf ρ (g : Matrix (Fin n) (Fin n) (Cinf E)) with hvdef
  have hS := isUnit_secMatInf ρ j hj v hgj
  have hne : rowCut ρ ((compGL w g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) (j w) ≠ 0 := by
    rw [← rowCutInf_apply]; exact hgj w
  have hcomp : compGL w (toGLInf (Matrix.of (secMatInf ρ j v))) =
      toGL (Matrix.of (secMat ρ (j w) (rowCut ρ ((compGL w g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)))) := by
    have hu := isUnit_secMat ρ (j w) (hj w) _ hne
    apply Units.ext
    rw [val_toGL hu]
    ext i l
    rw [compGL_apply, val_toGLInf hS]
    change secMat ρ (j w) (fun l => v l w) i l = _
    congr 1
    funext l
    exact rowCutInf_apply ρ g w l
  rw [map_mul, map_inv, hcomp]
  exact (secMat_main n ρ (j w) (hj w)).2.1 (compGL w g) (hg w) hne

end GlobalTheory.JSW.MirCinf
