import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.OmAtSmulRight
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.StdCharacterHalfSymplecticFormRealPointStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SmoothIffRealCoordinatesAndRealLines

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockCompare GlobalTheory.VacUnique

namespace GlobalTheory.VacUnique.Ann

theorem deriv_twisted_line {R : Type} [NormedAddCommGroup R] [NormedSpace ℝ R] (F : R → ℂ) (hF : Differentiable ℝ F)
    (om : R →ₗ[ℝ] R →ₗ[ℝ] ℝ) (w u : R) :
    deriv (fun t : ℝ => Complex.exp (-(Real.pi * Complex.I) * (om w (t • u) : ℂ)) * F (w + t • u)) 0 =
      fderiv ℝ F w u - Real.pi * Complex.I * (om w u : ℂ) * F w := by
  have h1 : HasDerivAt (fun t : ℝ => w + t • u) u 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const u).const_add w
  have h2 : HasDerivAt (fun t : ℝ => F (w + t • u)) (fderiv ℝ F w u) 0 := by
    have h := (hF (w + (0 : ℝ) • u)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
    simpa [Function.comp_def] using h
  have h3 : HasDerivAt (fun t : ℝ => -(Real.pi * Complex.I) * (om w (t • u) : ℂ))
      (-(Real.pi * Complex.I) * (om w u : ℂ)) 0 := by
    have e : (fun t : ℝ => -(Real.pi * Complex.I) * (om w (t • u) : ℂ)) =
        fun t : ℝ => (t : ℂ) * (-(Real.pi * Complex.I) * (om w u : ℂ)) := by
      funext t
      rw [LinearMap.map_smul, smul_eq_mul, Complex.ofReal_mul]
      ring
    rw [e]
    simpa using (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const (-(Real.pi * Complex.I) * (om w u : ℂ))
  have h4 := (h3.cexp.mul h2).deriv
  refine Eq.trans h4 ?_
  simp only [zero_smul, map_zero, Complex.ofReal_zero, mul_zero, Complex.exp_zero, add_zero, one_mul]
  ring

variable {D : D7} {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D}

open Classical in
theorem lineAt_eq (h : Chart θ σ) (S T : HSp D) (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (t : ℝ) :
    lineAt θ τ z t = iotaW σ T S (t • (Pi.single τ z : RW T S)) := by
  have hL : IsLineAt θ τ z (lineAt θ τ z) :=
    Classical.epsilon_spec (GlobalTheory.RealLineAt.lineAt_exists D θ h.inf T.rank S.rank τ z)
  refine h.real_ext (V := T) (W := S) (hL.2.1 t) (h.real_iota T S _) ?_
  rw [h.pi_iota]
  funext τ'
  refine (hL.2.2 t τ').trans ?_
  by_cases e : τ' = τ
  · subst e
    have e1 : (Pi.single τ' z : RW T S) τ' = z := Pi.single_eq_same _ _
    rw [if_pos rfl, Pi.smul_apply, e1]
    funext i j
    show (t : ℂ) * z i j = t • z i j
    exact (Complex.real_smul).symm
  · have e1 : (Pi.single τ z : RW T S) τ' = 0 := Pi.single_eq_of_ne e _
    rw [if_neg e, Pi.smul_apply, e1, smul_zero]
    rfl

open Classical in
theorem dRho_eq (h : Chart θ σ) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (S T : HSp D)
    (f : WO S T → ℂ) (hF : Differentiable ℝ fun z : RW T S => f (iotaW σ T S z)) (τ : D.what₂.Tau)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (w : RW T S) :
    Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f (iotaW σ T S w) =
      fderiv ℝ (fun z : RW T S => f (iotaW σ T S z)) w (Pi.single τ z) -
        Real.pi * Complex.I * (omO S T w (Pi.single τ z) : ℂ) * f (iotaW σ T S w) := by
  refine Eq.trans ?_ (deriv_twisted_line _ hF (omO S T) w (Pi.single τ z))
  unfold Formalism.IndefR.Datum.dRho
  congr 1
  funext t
  rw [lineAt_eq h S T τ z t]
  unfold heisO
  rw [GlobalTheory.T.stdCharacter_halfSymplecticForm_realPoint D θ ψ h.inf hψ S T _ _ (Or.inl (h.real_iota T S w)), h.pi_iota, h.pi_iota,
    (iotaW σ T S).map_add]

open Classical in
theorem jO_single (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (τ : D.what₂.Tau)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    jO S T sS sT (Pi.single τ z) = Pi.single τ (cplxO (sS τ) (sT τ) z) := by
  funext τ'
  rw [jO_apply]
  by_cases e : τ' = τ
  · subst e
    have e1 : ∀ y : Matrix (Fin T.rank) (Fin S.rank) ℂ, (Pi.single τ' y : RW T S) τ' = y :=
      fun _ => Pi.single_eq_same _ _
    rw [e1, e1]
  · have e1 : ∀ y : Matrix (Fin T.rank) (Fin S.rank) ℂ, (Pi.single τ y : RW T S) τ' = 0 :=
      fun _ => Pi.single_eq_of_ne e _
    rw [e1, e1]
    show Complex.I • (sT τ' * (0 : Matrix (Fin T.rank) (Fin S.rank) ℂ) * sS τ') = (0 : Matrix (Fin T.rank) (Fin S.rank) ℂ)
    rw [Matrix.mul_zero, Matrix.zero_mul, smul_zero]

theorem vacuum_annihilation : ∀ (D : D7) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D), Chart θ σ → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (f : WO S T → ℂ), IsThetaFunO ψ S T f → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) → Differentiable ℝ (fun z : RW T S => f (iotaW σ T S z)) ∧ ∀ w z : RW T S, (fderiv ℝ (fun z : RW T S => f (iotaW σ T S z)) w z - Real.pi * Complex.I * (omO S T w z : ℂ) * f (iotaW σ T S w)) + Complex.I * (fderiv ℝ (fun z : RW T S => f (iotaW σ T S z)) w (jO S T sS sT z) - Real.pi * Complex.I * (omO S T w (jO S T sS sT z) : ℂ) * f (iotaW σ T S w)) = 0 := by
  classical
  intro D θ σ h ψ hψ S T sS sT f hf hv
  have hF : Differentiable ℝ (fun z : RW T S => f (iotaW σ T S z)) := by
    have h1 := ((smooth_iff_sm_and_real_lines D θ σ h T S).1 f).1 hf.smooth 0
    simp only [zero_add] at h1
    exact h1.differentiable (by simp)
  refine ⟨hF, fun w z => ?_⟩
  let A : RW T S →+ ℂ :=
    { toFun := fun z => fderiv ℝ (fun z : RW T S => f (iotaW σ T S z)) w z -
        Real.pi * Complex.I * (omO S T w z : ℂ) * f (iotaW σ T S w)
      map_zero' := by simp
      map_add' := fun x y => by
        rw [ContinuousLinearMap.map_add, LinearMap.map_add, Complex.ofReal_add]
        ring }
  show A z + Complex.I * A (jO S T sS sT z) = 0
  rw [← Finset.univ_sum_single z, map_sum, map_sum, map_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun τ _ => ?_
  have h1 := congrFun (hv τ (z τ)) (iotaW σ T S w)
  have h2 : Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ (z τ) f (iotaW σ T S w) +
      Complex.I * Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ) (z τ)) f (iotaW σ T S w) = 0 := h1
  have h3 := dRho_eq h hψ S T f hF τ (z τ) w
  have h4 := dRho_eq h hψ S T f hF τ (cplxO (sS τ) (sT τ) (z τ)) w
  have h5 := jO_single S T sS sT τ (z τ)
  have h6 : A (Pi.single τ (z τ)) + Complex.I * A (Pi.single τ (cplxO (sS τ) (sT τ) (z τ))) = 0 :=
    (congrArg₂ (fun a b : ℂ => a + Complex.I * b) h3 h4).symm.trans h2
  exact (congrArg (fun b => A (Pi.single τ (z τ)) + Complex.I * A b) h5).trans h6

end GlobalTheory.VacUnique.Ann
