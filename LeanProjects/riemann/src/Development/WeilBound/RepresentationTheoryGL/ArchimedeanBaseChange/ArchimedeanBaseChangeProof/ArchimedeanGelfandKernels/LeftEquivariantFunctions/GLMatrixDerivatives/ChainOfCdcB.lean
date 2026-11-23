import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.ChainOfCdc

noncomputable section

open Matrix Finset
open scoped ContDiff

namespace PositivityTheory.RgBcC.LfSt.ChainPf.Cdc

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat hb)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem hb_conj_back (k : Matrix.unitaryGroup (Fin n) ℂ) (X : Mat n) :
    (k.1)ᴴ * ((k.1 * X * (k.1)ᴴ) * k.1) = X := by
  have h : (k.1)ᴴ * ((k.1 * X * (k.1)ᴴ) * k.1) = ((k.1)ᴴ * k.1) * X * ((k.1)ᴴ * k.1) := by
    simp only [Matrix.mul_assoc]
  rw [h, unit_star_mul]
  simp

theorem dCinCE : DCinCE := by
  intro n lam E Fr ε ι S Γ T hD f hf
  obtain ⟨hs, heq⟩ := hf
  have hdiff : ∀ x ∈ GLs n, DifferentiableAt ℝ f x := fun x hx =>
    (hs.differentiableOn (by simp)).differentiableAt (isOpen_GLs.mem_nhds hx)
  refine ⟨?_, ?_⟩
  · have hfa := contDiffOn_fderivWithin_apply (m := ∞) hs isOpen_GLs.uniqueDiffOn (le_of_eq rfl)
    unfold DC
    refine ContDiffOn.sum fun p _ => ?_
    have h1 : ContDiffOn ℝ ∞ (fun x => Rd (hb p) f x) (GLs n) := by
      refine (hfa.comp (contDiffOn_id.prodMk (mulRL (hb p)).contDiff.contDiffOn)
        (fun x hx => ⟨hx, Set.mem_univ _⟩)).congr fun x hx => ?_
      show fderiv ℝ f x (x * hb p) = fderivWithin ℝ f (GLs n) x (mulRL (hb p) x)
      rw [fderivWithin_of_isOpen isOpen_GLs hx, mulRL_apply]
    have h2 : ContDiffOn ℝ ∞ (fun x => fderiv ℝ Fr 1 (hb p) (f x)) (GLs n) :=
      ((fderiv ℝ Fr 1 (hb p)).restrictScalars ℝ).contDiff.comp_contDiffOn hs
    exact ((ε (hb p)).restrictScalars ℝ).contDiff.comp_contDiffOn (h1.add h2)
  · intro g hg k
    have hgk : g * k.1 ∈ GLs n := mem_GLs_mul hg (unit_mem k)
    have hRd : ∀ X : Mat n, Rd X f (g * k.1) = E.ρ k⁻¹ (Rd (k.1 * X * (k.1)ᴴ) f g) := by
      intro X
      have hev : (fun y : Mat n => f (y * k.1)) =ᶠ[nhds g]
          fun y => ((E.ρ k⁻¹).restrictScalars ℝ) (f y) := by
        filter_upwards [isOpen_GLs.mem_nhds hg] with y hy
        simpa using heq y hy k
      have h := fderiv_right f k.1 g _ (hdiff _ hgk) (hdiff _ hg) hev (g * (k.1 * X * (k.1)ᴴ))
      have hm : g * (k.1 * X * (k.1)ᴴ) * k.1 = g * k.1 * X := by
        simp only [Matrix.mul_assoc, unit_star_mul, Matrix.mul_one]
      show fderiv ℝ f (g * k.1) (g * k.1 * X) = E.ρ k⁻¹ (fderiv ℝ f g (g * (k.1 * X * (k.1)ᴴ)))
      rw [← hm]
      simpa using h
    have hv : ∀ v, E.ρ k (E.ρ k⁻¹ v) = v := by
      intro v
      rw [← ContinuousLinearMap.mul_apply, rho_mul_inv]
      rfl
    have hdF : ∀ (X : Mat n) (v : E.V), (fderiv ℝ Fr 1 X) (E.ρ k⁻¹ v)
        = E.ρ k⁻¹ (fderiv ℝ Fr 1 (k.1 * X * (k.1)ᴴ) v) := by
      intro X v
      have h := dFr_conj hD k (k.1 * X * (k.1)ᴴ)
      rw [hb_conj_back k X] at h
      rw [h, ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply, hv]
    have heps : ∀ (X : Mat n), IsHermitian X → ∀ w,
        ε X (E.ρ k⁻¹ w) = E.ρ k⁻¹ (ε (k.1 * X * (k.1)ᴴ) w) := by
      intro X hX w
      rw [← ContinuousLinearMap.mul_apply, eps_rho_inv hD k X hX, ContinuousLinearMap.mul_apply]
    let B : Mat n →ₗ[ℝ] Mat n →ₗ[ℝ] E.V :=
      LinearMap.mk₂ ℝ (fun Y Z => ε Y (Rd Z f g + fderiv ℝ Fr 1 Z (f g)))
        (by
          intro a b c
          simp only [map_add, ContinuousLinearMap.add_apply]
          abel)
        (by intro c a b; simp only [map_smul, ContinuousLinearMap.smul_apply])
        (by
          intro a b c
          simp only [Rd, Matrix.mul_add, map_add, ContinuousLinearMap.add_apply]
          abel)
        (by
          intro c a b
          simp only [Rd, Matrix.mul_smul, map_smul, ContinuousLinearMap.smul_apply]
          rw [← smul_add]
          exact (ε a).map_smul_of_tower c _)
    have key := basis_inv B k
    unfold DC
    rw [heq g hg k]
    calc ∑ p : Fin n × Fin n, ε (hb p) (Rd (hb p) f (g * k.1) + fderiv ℝ Fr 1 (hb p) (E.ρ k⁻¹ (f g)))
        = ∑ p : Fin n × Fin n, E.ρ k⁻¹ (B (k.1 * hb p * (k.1)ᴴ) (k.1 * hb p * (k.1)ᴴ)) := by
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [hRd, hdF, ← map_add, heps _ (hb_herm p)]
          rfl
      _ = E.ρ k⁻¹ (∑ p : Fin n × Fin n, B (hb p) (hb p)) := by rw [← map_sum, key]
      _ = _ := rfl

end PositivityTheory.RgBcC.LfSt.ChainPf.Cdc
