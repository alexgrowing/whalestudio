import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg

noncomputable section

open scoped ContDiff

namespace GlobalTheory.FockCompare

section

variable {G R : Type} [AddCommGroup G] [NormedAddCommGroup R] [NormedSpace ℝ R] [FiniteDimensional ℝ R]
  {ι : R →+ G} {π : G →+ R} {om : R →ₗ[ℝ] R →ₗ[ℝ] ℝ}

omit [FiniteDimensional ℝ R] in

theorem heisComm_coset (hπ : ∀ x, π (ι x) = x)
    (hf : ∀ (f : G → ℂ), Sm ι f → ∀ (u : R) (w : G), hD ι π om u f w =
      -(Real.pi * Complex.I) * (om (π w) u : ℝ) * f w + fderiv ℝ (fun x : R => f (w + ι x)) 0 u)
    (f : G → ℂ) (h : Sm ι f) (v : R) (w : G) :
    (fun x : R => hD ι π om v f (w + ι x)) = fun x : R =>
      -(Real.pi * Complex.I) * (om (π w + x) v : ℝ) * f (w + ι x) + fderiv ℝ (fun y : R => f (w + ι y)) x v := by
  funext x
  rw [hf f h, map_add, hπ]
  congr 2
  have e : (fun y : R => f (w + ι x + ι y)) = fun y : R => (fun z : R => f (w + ι z)) (x + y) := by
    funext y; simp only [map_add, add_assoc]
  rw [e, fderiv_comp_add_left (f := fun z : R => f (w + ι z)), add_zero]

theorem heisComm_hasFDerivAt_om (a v x : R) :
    HasFDerivAt (fun x : R => ((om (a + x) v : ℝ) : ℂ))
      (Complex.ofRealCLM.comp (LinearMap.toContinuousLinearMap (om.flip v))) x := by
  have h := (Complex.ofRealCLM.comp (LinearMap.toContinuousLinearMap (om.flip v))).hasFDerivAt (x := a + x)
  have h2 := h.comp x ((hasFDerivAt_id x).const_add a)
  rw [ContinuousLinearMap.comp_id] at h2
  exact h2

theorem heisComm_contDiff_om (a v : R) : ContDiff ℝ ∞ (fun x : R => ((om (a + x) v : ℝ) : ℂ)) :=
  (Complex.ofRealCLM.comp (LinearMap.toContinuousLinearMap (om.flip v))).contDiff.comp
    (contDiff_const.add contDiff_id)

theorem heisComm_second (hπ : ∀ x, π (ι x) = x)
    (hf : ∀ (f : G → ℂ), Sm ι f → ∀ (u : R) (w : G), hD ι π om u f w =
      -(Real.pi * Complex.I) * (om (π w) u : ℝ) * f w + fderiv ℝ (fun x : R => f (w + ι x)) 0 u)
    (f : G → ℂ) (h : Sm ι f) (u v : R) (w : G) :
    hD ι π om u (hD ι π om v f) w =
      -(Real.pi * Complex.I) * (om (π w) u : ℝ) *
        (-(Real.pi * Complex.I) * (om (π w) v : ℝ) * f w + fderiv ℝ (fun x : R => f (w + ι x)) 0 v) +
      (-(Real.pi * Complex.I) * (om u v : ℝ) * f w +
        -(Real.pi * Complex.I) * (om (π w) v : ℝ) * fderiv ℝ (fun x : R => f (w + ι x)) 0 u +
        fderiv ℝ (fderiv ℝ (fun x : R => f (w + ι x))) 0 u v) := by
  have hfd : ∀ w', ContDiff ℝ ∞ (fderiv ℝ (fun x : R => f (w' + ι x))) := fun w' =>
    (h w').fderiv_right (m := ∞) (by simp)
  have hs : Sm ι (hD ι π om v f) := by
    intro w'
    rw [heisComm_coset hπ hf f h v w']
    exact ((contDiff_const.mul (heisComm_contDiff_om _ _)).mul (h w')).add
      ((hfd w').clm_apply contDiff_const)
  rw [hf _ hs, hf f h v w, heisComm_coset hπ hf f h v w]
  congr 1
  have h1 : HasFDerivAt (fun x : R => f (w + ι x)) (fderiv ℝ (fun x : R => f (w + ι x)) 0) 0 :=
    ((h w).differentiable (by simp) 0).hasFDerivAt
  have h2 : HasFDerivAt (fderiv ℝ (fun x : R => f (w + ι x))) (fderiv ℝ (fderiv ℝ (fun x : R => f (w + ι x))) 0) 0 :=
    ((hfd w).differentiable (by simp) 0).hasFDerivAt
  have h3 := ((((heisComm_hasFDerivAt_om (om := om) (π w) v 0).const_mul (-(Real.pi * Complex.I))).mul h1).add
    (h2.clm_apply (hasFDerivAt_const v 0))).fderiv
  have h4 := congrArg (fun L => L u) h3
  refine Eq.trans h4 ?_
  simp
  ring

end

theorem heisenberg_derivative_commutator :
    ∀ (G R : Type) [AddCommGroup G] [NormedAddCommGroup R] [NormedSpace ℝ R] [FiniteDimensional ℝ R]
      (ι : R →+ G) (π : G →+ R) (om : R →ₗ[ℝ] R →ₗ[ℝ] ℝ), (∀ x, π (ι x) = x) →
      (∀ (f : G → ℂ), Sm ι f → ∀ (u : R) (w : G), hD ι π om u f w =
        -(Real.pi * Complex.I) * (om (π w) u : ℝ) * f w + fderiv ℝ (fun x : R => f (w + ι x)) 0 u) →
      (∀ u v, om v u = -om u v) → ∀ (f : G → ℂ), Sm ι f → ∀ u v : R,
      hD ι π om u (hD ι π om v f) - hD ι π om v (hD ι π om u f) =
        (-(2 * Real.pi * Complex.I) * (om u v : ℝ)) • f := by
  intro G R _ _ _ _ ι π om hπ hf ha f h u v
  funext w
  have hsym : IsSymmSndFDerivAt ℝ (fun x : R => f (w + ι x)) 0 :=
    (h w).contDiffAt.isSymmSndFDerivAt (by rw [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))
  rw [Pi.sub_apply, heisComm_second hπ hf f h u v, heisComm_second hπ hf f h v u, hsym u v, ha u v]
  simp only [Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

end GlobalTheory.FockCompare

end
