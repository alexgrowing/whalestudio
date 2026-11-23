import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.SecondFromFirstStatement

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh
open scoped ContDiff

namespace UpperTheory.V.Lit.Dr

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

private theorem smooth_of_formula {f : GL (Fin a) (Cinf E) → ℂ} {F : Lie E a → ℂ} (h : ∀ y, f y = F (toL y.val))
    (hF : ContDiffOn ℝ ∞ F (invSet E a)) : ContDiffOn ℝ ∞ (extGL f) (invSet E a) :=
  hF.congr fun _ hx => (extGL_eventuallyEq h hx).self_of_nhds

private theorem smooth_reg (σ : GL (Fin a) (Cinf E) → GL (Fin a) (Cinf E))
    (h1 : ∀ τ i j, ContDiffOn ℝ ∞ (extGL fun y => coord τ ((σ y).val i j)) (invSet E a))
    (h2 : ∀ τ, ContDiffOn ℝ ∞ (extGL fun y => (coord τ (σ y).val.det)⁻¹) (invSet E a))
    {f : GL (Fin a) (Cinf E) → ℂ} (hf : f ∈ regFun E a) :
    ContDiffOn ℝ ∞ (extGL fun y => f (σ y)) (invSet E a) := by
  induction hf using Algebra.adjoin_induction with
  | mem f hf =>
    obtain ⟨τ, i, j, rfl⟩ | ⟨τ, rfl⟩ := hf
    exacts [h1 τ i j, h2 τ]
  | algebraMap c => exact smooth_of_formula (F := fun _ => c) (fun _ => rfl) contDiffOn_const
  | add f g _ _ hf hg => exact smooth_of_formula (fun y => by simp [extGL_val]) (hf.add hg)
  | mul f g _ _ hf hg => exact smooth_of_formula (fun y => by simp [extGL_val]) (hf.mul hg)

private theorem smooth_det (τ : E →+* ℂ) : ContDiff ℝ ∞ fun x : Lie E a => coord τ (Matrix.of x).det :=
  (coordL τ).contDiff.comp contDiff_det

private theorem smooth_det_inv (τ : E →+* ℂ) :
    ContDiffOn ℝ ∞ (fun x : Lie E a => (coord τ (Matrix.of x).det)⁻¹) (invSet E a) :=
  (smooth_det τ).contDiffOn.inv fun _ hx => (((Matrix.isUnit_iff_isUnit_det _).1 hx).map (coord τ)).ne_zero

private theorem smooth_adj (τ : E →+* ℂ) (i j : Fin a) :
    ContDiff ℝ ∞ fun x : Lie E a => coord τ ((Matrix.of x).adjugate i j) := by
  have h : ContDiff ℝ ∞ fun x : Lie E a => (Function.update x j (Pi.single i 1) : Lie E a) := by
    refine contDiff_pi.2 fun k => ?_
    by_cases hk : k = j
    · subst hk
      simpa using contDiff_const
    · simpa [Function.update_of_ne hk] using contDiff_apply ℝ _ k
  simp only [Matrix.adjugate_apply]
  exact (smooth_det τ).comp h

omit [NumberField E] in
private theorem coord_inv_entry (τ : E →+* ℂ) (y : GL (Fin a) (Cinf E)) (i j : Fin a) :
    coord τ ((y⁻¹).val i j) = (coord τ y.val.det)⁻¹ * coord τ (y.val.adjugate i j) := by
  have hu : IsUnit y.val.det := (Matrix.isUnit_iff_isUnit_det _).1 y.isUnit
  have e : y.val.adjugate = y.val.det • (y⁻¹).val := by
    calc y.val.adjugate = (y.val.adjugate * y.val) * (y⁻¹).val := by
          rw [mul_assoc, Units.mul_inv, mul_one]
      _ = _ := by rw [Matrix.adjugate_mul, smul_mul_assoc, one_mul]
  rw [e, Matrix.smul_apply, smul_eq_mul, map_mul, inv_mul_cancel_left₀ (hu.map (coord τ)).ne_zero]

omit [NumberField E] in
private theorem coord_inv_det (τ : E →+* ℂ) (y : GL (Fin a) (Cinf E)) :
    (coord τ (y⁻¹).val.det)⁻¹ = coord τ y.val.det := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← map_mul, ← Matrix.det_mul, Units.inv_mul, Matrix.det_one, map_one]

theorem matSmooth : MatSmooth := by
  intro E _ _ a Ξ i j
  refine ⟨smooth_reg id (fun τ k l => ?_) (fun τ => ?_) (Ξ.reg i j),
    smooth_reg (fun y => y⁻¹) (fun τ k l => ?_) (fun τ => ?_) (Ξ.reg i j)⟩
  · exact smooth_of_formula (F := fun x => coordL τ (x k l)) (fun _ => rfl) (by fun_prop)
  · exact smooth_of_formula (fun _ => rfl) (smooth_det_inv τ)
  · exact smooth_of_formula (fun y => coord_inv_entry τ y k l) ((smooth_det_inv τ).mul (smooth_adj τ k l).contDiffOn)
  · exact smooth_of_formula (fun y => coord_inv_det τ y) (smooth_det τ).contDiffOn

end UpperTheory.V.Lit.Dr
