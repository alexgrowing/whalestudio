import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff

namespace GlobalTheory.Proof.flat_form_mul_pull_zero_section

variable {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem flatOf_zero (τ : Matrix (Fin g) (Fin g) ℂ) : flatOf τ 0 = 0 := by
  ext (i | i) <;> simp [flatOf, Matrix.vecMul, dotProduct]

theorem flat_mulN (τ : E → Matrix (Fin g) (Fin g) ℂ) (n : ℤ) (P : Pt E g) :
    flat τ (mulN n P) = (n : ℝ) • flat τ P := by
  ext (i | i) <;>
    simp [flat, flatOf, mulN, Matrix.vecMul, dotProduct, Finset.mul_sum, mul_sub, mul_assoc]

theorem symp_smul (c : ℝ) (w : Fin 2 → Fl g) : symp g (fun i => c • w i) = c ^ 2 * symp g w := by
  show riem (c • w 0) (c • w 1) = c ^ 2 * riem (w 0) (w 1)
  simp only [riem, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem dflat_inl (τ : E → Matrix (Fin g) (Fin g) ℂ) (b : E) :
    (dflat τ (b, 0)).comp (ContinuousLinearMap.inl ℝ E (Fin g → ℂ)) = 0 := by
  by_cases h : DifferentiableAt ℝ (flat τ) (b, 0)
  · have h1 := h.hasFDerivAt.comp b (hasFDerivAt_prodMk_left (𝕜 := ℝ) b (0 : Fin g → ℂ))
    have h2 : (flat τ ∘ fun e : E => (e, (0 : Fin g → ℂ))) = fun _ => 0 := by
      funext e; simp [flat, flatOf_zero]
    rw [h2] at h1
    exact (h1.unique (hasFDerivAt_const 0 b)).symm ▸ rfl
  · simp [dflat, fderiv_zero_of_not_differentiableAt h]

theorem dflat_zero_apply (τ : E → Matrix (Fin g) (Fin g) ℂ) (b : E) (u : E) :
    dflat τ (b, 0) (u, 0) = 0 := by
  have := congrArg (fun L : E →L[ℝ] Fl g => L u) (dflat_inl τ b)
  simpa using this

theorem fderiv_zeroSec (b : E) :
    fderiv ℝ (zeroSec g) b = ContinuousLinearMap.inl ℝ E (Fin g → ℂ) :=
  (hasFDerivAt_prodMk_left (𝕜 := ℝ) b (0 : Fin g → ℂ)).fderiv

theorem zeroSec_part (τ : E → Matrix (Fin g) (Fin g) ℂ) (b : E) :
    (om0 τ (zeroSec g b)).compContinuousLinearMap (fderiv ℝ (zeroSec g) b) = 0 := by
  ext v
  simp only [om0, fderiv_zeroSec, zeroSec, ContinuousAlternatingMap.compContinuousLinearMap_apply]
  have hc : (⇑(dflat τ (b, 0)) ∘ ⇑(ContinuousLinearMap.inl ℝ E (Fin g → ℂ)) ∘ v) = 0 := by
    funext i; simp [dflat_zero_apply]
  rw [hc, ContinuousAlternatingMap.map_zero]; rfl

theorem mulN_part (τ : E → Matrix (Fin g) (Fin g) ℂ) (n : ℤ) (P : Pt E g) :
    pull (mulN n) (om0 τ) P = ((n : ℝ) ^ 2) • om0 τ P := by
  by_cases hn : n = 0
  · subst hn
    have hm : (mulN 0 : Pt E g → Pt E g) =
        ⇑((ContinuousLinearMap.inl ℝ E (Fin g → ℂ)).comp
          (ContinuousLinearMap.fst ℝ E (Fin g → ℂ))) := by
      funext Q; simp [mulN]
    have hd : fderiv ℝ (mulN 0 : Pt E g → Pt E g) P =
        (ContinuousLinearMap.inl ℝ E (Fin g → ℂ)).comp
          (ContinuousLinearMap.fst ℝ E (Fin g → ℂ)) := by
      rw [hm]; exact ContinuousLinearMap.fderiv _
    ext v
    simp only [pull, om0, hd, ContinuousAlternatingMap.compContinuousLinearMap_apply,
      ContinuousAlternatingMap.smul_apply]
    have hc : (⇑(dflat τ (mulN 0 P)) ∘ ⇑((ContinuousLinearMap.inl ℝ E (Fin g → ℂ)).comp
        (ContinuousLinearMap.fst ℝ E (Fin g → ℂ))) ∘ v) = 0 := by
      funext i; simp [mulN, dflat_zero_apply]
    rw [hc, ContinuousAlternatingMap.map_zero]; simp
  · have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    let L : Pt E g →L[ℝ] Pt E g := (ContinuousLinearMap.fst ℝ E (Fin g → ℂ)).prod
      ((n : ℝ) • ContinuousLinearMap.snd ℝ E (Fin g → ℂ))
    let L' : Pt E g →L[ℝ] Pt E g := (ContinuousLinearMap.fst ℝ E (Fin g → ℂ)).prod
      ((n : ℝ)⁻¹ • ContinuousLinearMap.snd ℝ E (Fin g → ℂ))
    let e : Pt E g ≃L[ℝ] Pt E g := ContinuousLinearEquiv.equivOfInverse L L'
      (fun Q => by ext <;> simp [L, L', smul_smul, hn'])
      (fun Q => by ext <;> simp [L, L', smul_smul, hn'])
    have hm : (mulN n : Pt E g → Pt E g) = ⇑e := by
      funext Q
      simp [e, L, mulN, ContinuousLinearEquiv.equivOfInverse, Int.cast_smul_eq_zsmul]
    have hd : fderiv ℝ (mulN n : Pt E g → Pt E g) P = (e : Pt E g →L[ℝ] Pt E g) := by
      rw [hm]; exact e.fderiv
    have hf : flat τ ∘ ⇑e = (n : ℝ) • flat τ := by
      funext Q; rw [Function.comp_apply, ← hm, flat_mulN]; rfl
    have key : (dflat τ (mulN n P)).comp (e : Pt E g →L[ℝ] Pt E g) = (n : ℝ) • dflat τ P := by
      have h1 := e.comp_right_fderiv (f := flat τ) (x := P)
      rw [hf, fderiv_const_smul_field] at h1
      rw [hm]
      exact h1.symm
    have hk : ∀ u, dflat τ (mulN n P) (fderiv ℝ (mulN n) P u) = (n : ℝ) • dflat τ P u := by
      intro u
      rw [hd]
      exact congrArg (fun M : Pt E g →L[ℝ] Fl g => M u) key
    ext v
    simp only [pull, om0, ContinuousAlternatingMap.compContinuousLinearMap_apply,
      ContinuousAlternatingMap.smul_apply, smul_eq_mul]
    have hc : (⇑(dflat τ (mulN n P)) ∘ ⇑(fderiv ℝ (mulN n) P) ∘ v) =
        fun i => (n : ℝ) • dflat τ P (v i) := funext fun i => hk (v i)
    rw [hc, symp_smul]; rfl

theorem main : ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}, IsPeriodMap B τ → (∀ n : ℤ, ∀ P ∈ cov B g, pull (mulN n) (om0 τ) P = ((n : ℝ) ^ 2) • om0 τ P) ∧ (∀ b ∈ B, (om0 τ (zeroSec g b)).compContinuousLinearMap (fderiv ℝ (zeroSec g) b) = 0) := by
  intro g E _ _ _ B τ _
  exact ⟨fun n P _ => mulN_part τ n P, fun b _ => zeroSec_part τ b⟩

end GlobalTheory.Proof.flat_form_mul_pull_zero_section
