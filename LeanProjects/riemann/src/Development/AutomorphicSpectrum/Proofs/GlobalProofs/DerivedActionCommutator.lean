import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsSmoothVec
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LieAlgebraOfLinearGroupClosedStatement

noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.CompanionTheory.Hypotheses₂.HCA.Bracket

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def rightMul (Y : Matrix (Fin n) (Fin n) ℂ) : (Fin n → Fin n → ℂ) →L[ℝ] (Fin n → Fin n → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z => Matrix.of.symm (Matrix.of z * Y)
      map_add' := fun x y => by
        ext a b
        simp [Matrix.mul_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := fun r x => by
        ext a b
        simp [Matrix.mul_apply, Finset.mul_sum, mul_assoc] }

theorem rightMul_apply (Y : Matrix (Fin n) (Fin n) ℂ) (z : Fin n → Fin n → ℂ) :
    rightMul Y z = Matrix.of.symm (Matrix.of z * Y) := rfl

open scoped Matrix.Norms.Operator in
theorem hasDerivAt_entry (X : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    HasDerivAt (fun t : ℝ => (NormedSpace.exp (t • X)) i j) (X i j) 0 := by
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)
  simp only [zero_smul, NormedSpace.exp_zero, one_mul] at h
  let L : Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℂ :=
    LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ i j)
  exact L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h

theorem hasDerivAt_curve (z : Fin n → Fin n → ℂ) (X : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun t : ℝ => (Matrix.of.symm (Matrix.of z * NormedSpace.exp (t • X)) : Fin n → Fin n → ℂ))
      (rightMul X z) 0 := by
  rw [hasDerivAt_pi]
  intro a
  rw [hasDerivAt_pi]
  intro b
  simp only [rightMul_apply, Matrix.of_symm_apply, Matrix.mul_apply, Matrix.of_apply]
  exact HasDerivAt.fun_sum (fun c _ => (hasDerivAt_entry X c b).const_mul (z a c))

def one : Fin n → Fin n → ℂ := Matrix.of.symm (1 : Matrix (Fin n) (Fin n) ℂ)

theorem of_one : Matrix.of (one (n := n)) = 1 := by simp [one]

section Smooth

variable {G : Set (Matrix (Fin n) (Fin n) ℂ)} {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {v : H}
  {F : (Fin n → Fin n → ℂ) → H}

theorem hasDerivAt_along (hG : IsLinRed G) (hF : ContDiff ℝ ∞ F)
    (hFv : ∀ z, Matrix.of z ∈ G → π (Matrix.of z) v = F z) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : X ∈ HCSS.lieOf G) {z : Fin n → Fin n → ℂ} (hz : Matrix.of z ∈ G) :
    HasDerivAt (fun t : ℝ => π (Matrix.of z * NormedSpace.exp (t • X)) v)
      (fderiv ℝ F z (rightMul X z)) 0 := by
  have hd : HasFDerivAt F (fderiv ℝ F z) (Matrix.of.symm (Matrix.of z * NormedSpace.exp ((0 : ℝ) • X))) := by
    have : (Matrix.of.symm (Matrix.of z * NormedSpace.exp ((0 : ℝ) • X)) : Fin n → Fin n → ℂ) = z := by
      simp
    rw [this]
    exact (hF.differentiable (by simp) z).hasFDerivAt
  have h := hd.comp_hasDerivAt (0 : ℝ) (hasDerivAt_curve z X)
  refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  have hm : Matrix.of z * NormedSpace.exp (t • X) ∈ G := hG.mul_mem _ hz _ (hX t)
  have := hFv (Matrix.of.symm (Matrix.of z * NormedSpace.exp (t • X))) (by simpa using hm)
  simpa using this

theorem hasDerivAt_exp_along (hG : IsLinRed G) (hF : ContDiff ℝ ∞ F)
    (hFv : ∀ z, Matrix.of z ∈ G → π (Matrix.of z) v = F z) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : X ∈ HCSS.lieOf G) :
    HasDerivAt (fun t : ℝ => π (NormedSpace.exp (t • X)) v) (fderiv ℝ F one (rightMul X one)) 0 := by
  have h := hasDerivAt_along hG hF hFv hX (z := one) (by rw [of_one]; exact hG.one_mem)
  simpa [of_one] using h

theorem dRep_eq (hG : IsLinRed G) (hF : ContDiff ℝ ∞ F)
    (hFv : ∀ z, Matrix.of z ∈ G → π (Matrix.of z) v = F z) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : X ∈ HCSS.lieOf G) : dRep π X v = fderiv ℝ F one (rightMul X one) :=
  (hasDerivAt_exp_along hG hF hFv hX).deriv

theorem rep_dRep (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) (hF : ContDiff ℝ ∞ F)
    (hFv : ∀ z, Matrix.of z ∈ G → π (Matrix.of z) v = F z) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : X ∈ HCSS.lieOf G) {z : Fin n → Fin n → ℂ} (hz : Matrix.of z ∈ G) :
    π (Matrix.of z) (dRep π X v) = fderiv ℝ F z (rightMul X z) := by
  have h1 := hasDerivAt_exp_along hG hF hFv hX
  have h2 := ((π (Matrix.of z)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
  have h3 := hasDerivAt_along hG hF hFv hX hz
  rw [dRep_eq hG hF hFv hX]
  refine HasDerivAt.unique ?_ h3
  refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  have := hrep.2 _ hz _ (hX t)
  simp [this]

theorem dRep_dRep (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) (hF : ContDiff ℝ ∞ F)
    (hFv : ∀ z, Matrix.of z ∈ G → π (Matrix.of z) v = F z) {X Y : Matrix (Fin n) (Fin n) ℂ}
    (hX : X ∈ HCSS.lieOf G) (hY : Y ∈ HCSS.lieOf G) :
    dRep π X (dRep π Y v) =
      fderiv ℝ (fderiv ℝ F) one (rightMul X one) (rightMul Y one) +
        fderiv ℝ F one (rightMul Y (rightMul X one)) := by
  have hF1 : ContDiff ℝ 1 (fderiv ℝ F) := hF.fderiv_right (by norm_cast)
  have hdF : HasFDerivAt (fderiv ℝ F) (fderiv ℝ (fderiv ℝ F) one) one :=
    (hF1.differentiable (by simp) one).hasFDerivAt
  have hG1 := hdF.clm_apply (rightMul Y).hasFDerivAt
  have hc := hasDerivAt_curve (one (n := n)) X
  have h0 : (Matrix.of.symm (Matrix.of (one (n := n)) * NormedSpace.exp ((0 : ℝ) • X)) : Fin n → Fin n → ℂ) = one := by
    simp [one]
  have h := hG1.comp_hasDerivAt_of_eq (0 : ℝ) hc h0.symm
  have h' : HasDerivAt (fun t : ℝ => π (NormedSpace.exp (t • X)) (dRep π Y v)) _ 0 :=
    h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => by
      have := rep_dRep hG hrep hF hFv hY (z := Matrix.of.symm (NormedSpace.exp (t • X)))
        (by simpa using hX t)
      simpa [of_one, Function.comp_def] using this)
  refine h'.deriv.trans ?_
  simp [add_comm]

end Smooth

theorem dRep_bracket {G : Set (Matrix (Fin n) (Fin n) ℂ)} {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) {v : H} (hv : IsSmoothVec G π v)
    {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ HCSS.lieOf G) (hY : Y ∈ HCSS.lieOf G) :
    dRep π (X * Y - Y * X) v = dRep π X (dRep π Y v) - dRep π Y (dRep π X v) := by
  obtain ⟨F, hF, hFv⟩ := hv
  have hZ : X * Y - Y * X ∈ HCSS.lieOf G := (GlobalTheory.T.lie_algebra_of_linear_group_closed hG).2.2.1 X Y hX hY
  have hsymm : IsSymmSndFDerivAt ℝ F one :=
    (hF.contDiffAt).isSymmSndFDerivAt (by
      simp only [minSmoothness_of_isRCLikeNormedField]
      exact WithTop.coe_le_coe.2 le_top)
  rw [dRep_dRep hG hrep hF hFv hX hY, dRep_dRep hG hrep hF hFv hY hX, dRep_eq hG hF hFv hZ,
    hsymm.eq (rightMul X one) (rightMul Y one), add_sub_add_left_eq_sub, ← map_sub]
  congr 1
  ext a b
  simp [rightMul_apply, one, Matrix.sub_apply]

theorem smooth_bracket : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) {v : H} (hv : IsSmoothVec G π v) {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ HCSS.lieOf G) (hY : Y ∈ HCSS.lieOf G), dRep π (X * Y - Y * X) v = dRep π X (dRep π Y v) - dRep π Y (dRep π X v) :=
  fun hG hrep _ hv _ _ hX hY => dRep_bracket hG hrep hv hX hY

end GlobalTheory.CompanionTheory.Hypotheses₂.HCA.Bracket

end
