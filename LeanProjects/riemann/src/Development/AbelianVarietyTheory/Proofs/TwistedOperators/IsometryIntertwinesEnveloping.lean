import Mathlib
import Formalism.PeriodIntegrals.DSInfCharCap
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.RealPlaceAnalysis.StatementE
import Formalism.RealPlaceAnalysis.StatementB
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LanglandsClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrOfNotMem
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)
open GlobalTheory.RealInd.Stages Finset GlobalTheory.FlagMeas Formalism.REAL

namespace GlobalTheory.ActUIso

variable {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']

theorem adjoint_comp_isometry (T : H' →ₗᵢ[ℂ] H) (v : H') :
    (ContinuousLinearMap.adjoint T.toContinuousLinearMap) (T v) = v := by
  apply ext_inner_right ℂ
  intro u
  rw [ContinuousLinearMap.adjoint_inner_left]
  simp

theorem deriv_isometry_comp (T : H' →ₗᵢ[ℂ] H) (f : ℝ → H') (t : ℝ) :
    deriv (fun s => T (f s)) t = T (deriv f t) := by
  by_cases hf : DifferentiableAt ℝ f t
  · have := (T.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hf.hasDerivAt
    exact this.deriv
  · have hTf : ¬ DifferentiableAt ℝ (fun s => T (f s)) t := by
      intro h
      apply hf
      have h2 := ((ContinuousLinearMap.adjoint T.toContinuousLinearMap).restrictScalars ℝ).differentiableAt.comp t h
      have e : f = (⇑(ContinuousLinearMap.restrictScalars ℝ (ContinuousLinearMap.adjoint T.toContinuousLinearMap)) ∘ fun s ↦ T (f s)) := by
        funext s
        simp [adjoint_comp_isometry]
      rw [e]; exact h2
    rw [deriv_zero_of_not_differentiableAt hf, deriv_zero_of_not_differentiableAt hTf, map_zero]

end GlobalTheory.ActUIso

namespace GlobalTheory.ActUIso

variable {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']

theorem inG_smul_add_theta {n : ℕ} (ε : Fin n → Bool) (Y : Matrix (Fin n) (Fin n) ℂ) :
    inG ε ((1 / 2 : ℂ) • (Y + PI.DSInfCharCap.thetaJ ε Y)) := by
  have hJ := Jm_conjTranspose ε
  have hJJ := Jm_mul_self ε
  unfold inG PI.DSInfCharCap.thetaJ
  set J := Jm ε
  have hs : star (1 / 2 : ℂ) = 1 / 2 := by simp
  rw [Matrix.conjTranspose_smul, hs, Matrix.smul_mul, Matrix.mul_smul, ← smul_add]
  have : (Y + -(J * Yᴴ * J))ᴴ * J + J * (Y + -(J * Yᴴ * J)) = 0 := by
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_neg, Matrix.conjTranspose_mul, hJ,
      Matrix.conjTranspose_conjTranspose, Matrix.add_mul, Matrix.mul_add, Matrix.neg_mul, Matrix.mul_neg,
      Matrix.mul_assoc, hJJ, Matrix.mul_one]
    rw [← Matrix.mul_assoc J J, hJJ, Matrix.one_mul]
    abel
  rw [this, smul_zero]

theorem inG_smul_sub_theta {n : ℕ} (ε : Fin n → Bool) (Y : Matrix (Fin n) (Fin n) ℂ) :
    inG ε ((1 / (2 * Complex.I)) • (Y - PI.DSInfCharCap.thetaJ ε Y)) := by
  have hJ := Jm_conjTranspose ε
  have hJJ := Jm_mul_self ε
  unfold inG PI.DSInfCharCap.thetaJ
  set J := Jm ε
  have hs : star (1 / (2 * Complex.I)) = -(1 / (2 * Complex.I)) := by
    simp [Complex.conj_I]
  rw [Matrix.conjTranspose_smul, hs, Matrix.smul_mul, Matrix.mul_smul, neg_smul, neg_add_eq_sub, ← smul_sub]
  have : J * (Y - -(J * Yᴴ * J)) - (Y - -(J * Yᴴ * J))ᴴ * J = 0 := by
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_neg, Matrix.conjTranspose_mul, hJ,
      Matrix.conjTranspose_conjTranspose, Matrix.sub_mul, Matrix.mul_sub, Matrix.neg_mul, Matrix.mul_neg,
      Matrix.mul_assoc, hJJ, Matrix.mul_one]
    rw [← Matrix.mul_assoc J J, hJJ, Matrix.one_mul]
    abel
  rw [this, smul_zero]

theorem dsig_intertwine {n : ℕ} (ε : Fin n → Bool)
    (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (ρ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H'))
    (T : H' →ₗᵢ[ℂ] H) (hT : ∀ (g : UJ ε) (w : H'), T (ρ' (uMat g) w) = ρ (uMat g) (T w))
    (X : Matrix (Fin n) (Fin n) ℂ) (hX : inG ε X) (w : H') :
    PI.PhMeasCore.dsig ρ X (T w) = T (PI.PhMeasCore.dsig ρ' X w) := by
  unfold PI.PhMeasCore.dsig
  have e : (fun t : ℝ => ρ (NormedSpace.exp ((t : ℂ) • X)) (T w)) =
      fun t : ℝ => T (ρ' (NormedSpace.exp ((t : ℂ) • X)) w) := by
    funext t
    have h := hT (expG ε X t) w
    have h2 : uMat (expG ε X t) = NormedSpace.exp ((t : ℂ) • X) := toM_expG ε X t hX
    rw [h2] at h
    exact h.symm
  rw [e, deriv_isometry_comp]

theorem dsigC_intertwine {n : ℕ} (ε : Fin n → Bool)
    (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (ρ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H'))
    (T : H' →ₗᵢ[ℂ] H) (hT : ∀ (g : UJ ε) (w : H'), T (ρ' (uMat g) w) = ρ (uMat g) (T w))
    (Y : Matrix (Fin n) (Fin n) ℂ) (w : H') :
    PI.DSInfCharCap.dsigC ε ρ Y (T w) = T (PI.DSInfCharCap.dsigC ε ρ' Y w) := by
  unfold PI.DSInfCharCap.dsigC
  rw [dsig_intertwine ε ρ ρ' T hT _ (inG_smul_add_theta ε Y),
    dsig_intertwine ε ρ ρ' T hT _ (inG_smul_sub_theta ε Y), map_add, map_smul]

theorem dsigCW_intertwine {n : ℕ} (ε : Fin n → Bool)
    (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (ρ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H'))
    (T : H' →ₗᵢ[ℂ] H) (hT : ∀ (g : UJ ε) (w : H'), T (ρ' (uMat g) w) = ρ (uMat g) (T w))
    (l : List (Matrix (Fin n) (Fin n) ℂ)) (w : H') :
    PI.DSInfCharCap.dsigCW ε ρ l (T w) = T (PI.DSInfCharCap.dsigCW ε ρ' l w) := by
  induction l with
  | nil => rfl
  | cons Y l ih =>
    simp only [PI.DSInfCharCap.dsigCW]
    rw [ih, dsigC_intertwine ε ρ ρ' T hT]

theorem actU_isometry : ∀ {n : ℕ} (ε : Fin n → Bool) {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H'] (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (ρ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')) (T : H' →ₗᵢ[ℂ] H), (∀ (g : UJ ε) (w : H'), T (ρ' (uMat g) w) = ρ (uMat g) (T w)) → ∀ (p : FreeAlgebra ℂ (Fin n × Fin n)) (w : H'), actU ε ρ p (T w) = T (actU ε ρ' p w) := by
  intro n ε H H' _ _ _ _ _ _ ρ ρ' T hT p w
  unfold actU
  simp only [Finsupp.sum, map_sum, map_smul, dsigCW_intertwine ε ρ ρ' T hT]

end GlobalTheory.ActUIso
