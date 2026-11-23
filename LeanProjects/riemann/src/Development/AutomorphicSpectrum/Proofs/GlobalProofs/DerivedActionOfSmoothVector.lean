import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsSmoothVec
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.HCA.SmoothDeriv

open scoped Matrix.Norms.Operator

variable {n : ℕ}

def coord : Matrix (Fin n) (Fin n) ℂ →L[ℝ] (Fin n → Fin n → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => Matrix.of.symm A
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

theorem coord_apply (A : Matrix (Fin n) (Fin n) ℂ) : coord A = Matrix.of.symm A := rfl

theorem hasDerivAt_coord_mul_exp (g X : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun t : ℝ => coord (g * NormedSpace.exp (t • X))) (coord (g * X)) 0 := by
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)
  simp only [zero_smul, NormedSpace.exp_zero, one_mul] at h
  exact coord.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (h.const_mul g)

theorem contDiff_mul_right (X : Matrix (Fin n) (Fin n) ℂ) :
    ContDiff ℝ ∞ (fun z : Fin n → Fin n → ℂ => Matrix.of.symm (Matrix.of z * X)) := by
  refine contDiff_pi.2 fun a => contDiff_pi.2 fun b => ?_
  have e : (fun z : Fin n → Fin n → ℂ => Matrix.of.symm (Matrix.of z * X) a b) =
      fun z => ∑ c, z a c * X c b := by
    funext z
    simp [Matrix.mul_apply]
  rw [e]
  refine ContDiff.sum fun c _ => ContDiff.mul ?_ contDiff_const
  exact (contDiff_apply ℝ ℂ c).comp (contDiff_apply ℝ (Fin n → ℂ) a)

end GlobalTheory.CompanionTheory.Hypotheses₂.HCA.SmoothDeriv

namespace GlobalTheory.CompanionTheory.Hypotheses₂.HCA

open SmoothDeriv

theorem hasDerivAt_dRep_and_isSmoothVec : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G)
    (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) {v : H} (hv : IsSmoothVec G π v) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : X ∈ HCSS.lieOf G),
    HasDerivAt (fun t : ℝ => π (NormedSpace.exp (t • X)) v) (dRep π X v) 0 ∧
      IsSmoothVec G π (dRep π X v) := by
  intro n G H _ _ π hG hrep v hv X hX
  obtain ⟨F, hF, hFG⟩ := hv
  have hFd : Differentiable ℝ F := hF.differentiable (by simp)

  have key : ∀ g ∈ G, HasDerivAt (fun t : ℝ => π g (π (NormedSpace.exp (t • X)) v))
      (fderiv ℝ F (Matrix.of.symm g) (coord (g * X))) 0 := by
    intro g hg
    have h1 := ((hFd (Matrix.of.symm g)).hasFDerivAt)
    have h2 : HasFDerivAt F (fderiv ℝ F (Matrix.of.symm g)) (coord (g * NormedSpace.exp ((0 : ℝ) • X))) := by
      simpa [coord_apply] using h1
    have h3 := h2.comp_hasDerivAt (0 : ℝ) (hasDerivAt_coord_mul_exp g X)
    refine h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
    have hm : g * NormedSpace.exp (t • X) ∈ G := hG.mul_mem g hg _ (hX t)
    have := hFG (Matrix.of.symm (g * NormedSpace.exp (t • X))) (by simpa using hm)
    simp only [Equiv.apply_symm_apply] at this
    simp only [Function.comp, coord_apply]
    rw [← this, hrep.2 g hg _ (hX t)]
    rfl
  have h1 : HasDerivAt (fun t : ℝ => π (NormedSpace.exp (t • X)) v)
      (fderiv ℝ F (Matrix.of.symm 1) (coord (1 * X))) 0 := by
    have := key 1 hG.one_mem
    simpa [hrep.1] using this
  have hd : dRep π X v = fderiv ℝ F (Matrix.of.symm 1) (coord (1 * X)) := h1.deriv
  have h1' : HasDerivAt (fun t : ℝ => π (NormedSpace.exp (t • X)) v) (dRep π X v) 0 := by
    rw [hd]; exact h1
  refine ⟨h1', fun z => fderiv ℝ F z (Matrix.of.symm (Matrix.of z * X)), ?_, ?_⟩
  · exact (hF.fderiv_right (m := ∞) (by simp)).clm_apply (contDiff_mul_right X)
  · intro z hz
    have h2 := ((π (Matrix.of z)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1'
    exact h2.unique (key _ hz)

end GlobalTheory.CompanionTheory.Hypotheses₂.HCA

end
