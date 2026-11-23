import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjMono
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.StdCharacterHalfSymplecticFormRealPoint
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FockVacuumAnnihilationEquationRealCoordinates
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockTransl
open Formalism.L2.Ker (VCx DVar derivAt0)

namespace GlobalTheory.HeisTranslCR

open GlobalTheory.FockCompare GlobalTheory.VacUnique

theorem deriv_twisted_line_at {R : Type} [NormedAddCommGroup R] [NormedSpace ℝ R] (F : R → ℂ) (hF : Differentiable ℝ F)
    (om : R →ₗ[ℝ] R →ₗ[ℝ] ℝ) (a w u : R) :
    deriv (fun t : ℝ => Complex.exp (-(Real.pi * Complex.I) * (om a (t • u) : ℂ)) * F (w + t • u)) 0 =
      fderiv ℝ F w u - Real.pi * Complex.I * (om a u : ℂ) * F w := by
  have h1 : HasDerivAt (fun t : ℝ => w + t • u) u 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const u).const_add w
  have h2 : HasDerivAt (fun t : ℝ => F (w + t • u)) (fderiv ℝ F w u) 0 := by
    have h := (hF (w + (0 : ℝ) • u)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
    simpa [Function.comp_def] using h
  have h3 : HasDerivAt (fun t : ℝ => -(Real.pi * Complex.I) * (om a (t • u) : ℂ))
      (-(Real.pi * Complex.I) * (om a u : ℂ)) 0 := by
    have e : (fun t : ℝ => -(Real.pi * Complex.I) * (om a (t • u) : ℂ)) =
        fun t : ℝ => (t : ℂ) * (-(Real.pi * Complex.I) * (om a u : ℂ)) := by
      funext t
      rw [LinearMap.map_smul, smul_eq_mul, Complex.ofReal_mul]
      ring
    rw [e]
    simpa using (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const (-(Real.pi * Complex.I) * (om a u : ℂ))
  have h4 := (h3.cexp.mul h2).deriv
  refine Eq.trans h4 ?_
  simp only [zero_smul, map_zero, Complex.ofReal_zero, mul_zero, Complex.exp_zero, add_zero, one_mul]
  ring

theorem differentiable_phase {R : Type} [NormedAddCommGroup R] [NormedSpace ℝ R] [FiniteDimensional ℝ R]
    (om : R →ₗ[ℝ] R →ₗ[ℝ] ℝ) (a : R) :
    Differentiable ℝ fun w : R => Complex.exp (-(Real.pi * Complex.I) * (om a w : ℂ)) := by
  have h : Differentiable ℝ fun w : R => ((om a w : ℝ) : ℂ) :=
    Complex.ofRealCLM.differentiable.comp (LinearMap.toContinuousLinearMap (om a)).differentiable
  exact ((differentiable_const _).mul h).cexp

theorem fderiv_phase_mul {R : Type} [NormedAddCommGroup R] [NormedSpace ℝ R] [FiniteDimensional ℝ R] (F : R → ℂ)
    (hF : Differentiable ℝ F) (om : R →ₗ[ℝ] R →ₗ[ℝ] ℝ) (a w u : R) :
    fderiv ℝ (fun w : R => Complex.exp (-(Real.pi * Complex.I) * (om a w : ℂ)) * F w) w u =
      Complex.exp (-(Real.pi * Complex.I) * (om a w : ℂ)) *
        (fderiv ℝ F w u - Real.pi * Complex.I * (om a u : ℂ) * F w) := by
  have hG : Differentiable ℝ fun w : R => Complex.exp (-(Real.pi * Complex.I) * (om a w : ℂ)) * F w :=
    (differentiable_phase om a).mul hF
  have h1 : HasDerivAt (fun t : ℝ => w + t • u) u 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const u).const_add w
  have h2 := (hG (w + (0 : ℝ) • u)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
  simp only [zero_smul, add_zero, Function.comp_def] at h2
  rw [← h2.deriv]
  have e : (fun t : ℝ => Complex.exp (-(Real.pi * Complex.I) * (om a (w + t • u) : ℂ)) * F (w + t • u)) =
      fun t : ℝ => Complex.exp (-(Real.pi * Complex.I) * (om a w : ℂ)) *
        (Complex.exp (-(Real.pi * Complex.I) * (om a (t • u) : ℂ)) * F (w + t • u)) := by
    funext t
    rw [LinearMap.map_add, Complex.ofReal_add, mul_add, Complex.exp_add]
    ring
  rw [e, deriv_const_mul_field, deriv_twisted_line_at F hF om a w u]

variable {D : D7} {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D}

theorem heisO_real_at (h : Chart θ σ) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (S T : HSp D)
    (f : WO S T → ℂ) (y : WO S T) (w : RW T S) :
    heisO ψ S T (iotaW σ T S w) f y =
      Complex.exp (-(Real.pi * Complex.I) * (omO S T (piW θ T S y) w : ℂ)) * f (y + iotaW σ T S w) := by
  unfold heisO
  rw [GlobalTheory.OrientedChar.char_symplOH D θ ψ h.inf hψ S T _ _ (Or.inr (h.real_iota T S w)), h.pi_iota]

open Classical in

theorem dRho_eq_at (h : Chart θ σ) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (S T : HSp D)
    (f : WO S T → ℂ) (y : WO S T) (hF : Differentiable ℝ fun v : RW T S => f (y + iotaW σ T S v)) (τ : D.what₂.Tau)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (w : RW T S) :
    Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f (y + iotaW σ T S w) =
      fderiv ℝ (fun v : RW T S => f (y + iotaW σ T S v)) w (Pi.single τ z) -
        Real.pi * Complex.I * (omO S T (piW θ T S y + w) (Pi.single τ z) : ℂ) * f (y + iotaW σ T S w) := by
  refine Eq.trans ?_ (deriv_twisted_line_at _ hF (omO S T) (piW θ T S y + w) w (Pi.single τ z))
  unfold Formalism.IndefR.Datum.dRho
  congr 1
  funext t
  rw [GlobalTheory.VacUnique.Ann.lineAt_eq h S T τ z t, heisO_real_at h hψ, (piW θ T S).map_add, h.pi_iota, add_assoc,
    ← (iotaW σ T S).map_add]

open Classical in

theorem heis_translate_cauchy_riemann : ∀ (D : D7) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D), GlobalTheory.FockCompare.Chart θ σ → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (f : WO S T → ℂ), GlobalTheory.ChainFr.IsVacF ψ θ A B f → ∀ y : WO S T, Differentiable ℝ (fun w : GlobalTheory.FockCompare.RW T S => heisO ψ S T (GlobalTheory.FockCompare.iotaW σ T S w) f y) ∧ ∀ w z : GlobalTheory.FockCompare.RW T S, fderiv ℝ (fun w : GlobalTheory.FockCompare.RW T S => heisO ψ S T (GlobalTheory.FockCompare.iotaW σ T S w) f y) w z + Complex.I * fderiv ℝ (fun w : GlobalTheory.FockCompare.RW T S => heisO ψ S T (GlobalTheory.FockCompare.iotaW σ T S w) f y) w (GlobalTheory.VacUnique.jO S T A.cart B.cart z) = (Real.pi : ℂ) * Complex.I * ((GlobalTheory.VacUnique.omO S T w z : ℂ) + Complex.I * (GlobalTheory.VacUnique.omO S T w (GlobalTheory.VacUnique.jO S T A.cart B.cart z) : ℂ)) * heisO ψ S T (GlobalTheory.FockCompare.iotaW σ T S w) f y := by
  intro D θ σ h ψ hψ S T A B f hf y
  have hF : Differentiable ℝ fun v : RW T S => f (y + iotaW σ T S v) :=
    (GlobalTheory.OrientedHeis.theta_sm h hf.1 y).differentiable (by simp)
  have hG : (fun w : RW T S => heisO ψ S T (iotaW σ T S w) f y) = fun w : RW T S =>
      Complex.exp (-(Real.pi * Complex.I) * (omO S T (piW θ T S y) w : ℂ)) * f (y + iotaW σ T S w) := by
    funext w
    exact heisO_real_at h hψ S T f y w
  rw [hG]
  refine ⟨(differentiable_phase (omO S T) (piW θ T S y)).mul hF, fun w z => ?_⟩
  rw [fderiv_phase_mul _ hF, fderiv_phase_mul _ hF]
  rw [heisO_real_at h hψ S T f y w]
  set a := piW θ T S y with ha
  set Fd := fderiv ℝ (fun v : RW T S => f (y + iotaW σ T S v)) w with hFd
  set Fw := f (y + iotaW σ T S w) with hFw
  let L : RW T S →+ ℂ :=
    { toFun := fun s => Fd s - Real.pi * Complex.I * (omO S T (a + w) s : ℂ) * Fw
      map_zero' := by simp
      map_add' := fun x x' => by
        rw [ContinuousLinearMap.map_add, LinearMap.map_add, Complex.ofReal_add]
        ring }
  have hL : L z + Complex.I * L (jO S T A.cart B.cart z) = 0 := by
    rw [← Finset.univ_sum_single z, map_sum, map_sum, map_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun τ _ => ?_
    have h1 := congrFun (hf.2 τ (z τ)) (y + iotaW σ T S w)
    have h2 : Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ (z τ) f (y + iotaW σ T S w) +
        Complex.I * Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ (cplxO (A.cart τ) (B.cart τ) (z τ)) f
          (y + iotaW σ T S w) = 0 := h1
    have h3 := dRho_eq_at h hψ S T f y hF τ (z τ) w
    have h4 := dRho_eq_at h hψ S T f y hF τ (cplxO (A.cart τ) (B.cart τ) (z τ)) w
    have h5 := GlobalTheory.VacUnique.Ann.jO_single S T A.cart B.cart τ (z τ)
    have h6 : L (Pi.single τ (z τ)) + Complex.I * L (Pi.single τ (cplxO (A.cart τ) (B.cart τ) (z τ))) = 0 :=
      (congrArg₂ (fun a b : ℂ => a + Complex.I * b) h3 h4).symm.trans h2
    exact (congrArg (fun b => L (Pi.single τ (z τ)) + Complex.I * L b) h5).trans h6
  have e1 : L z = Fd z - Real.pi * Complex.I * ((omO S T a z : ℂ) + (omO S T w z : ℂ)) * Fw := by
    show Fd z - Real.pi * Complex.I * (omO S T (a + w) z : ℂ) * Fw = _
    rw [LinearMap.map_add, LinearMap.add_apply, Complex.ofReal_add]
  have e2 : L (jO S T A.cart B.cart z) = Fd (jO S T A.cart B.cart z) - Real.pi * Complex.I *
      ((omO S T a (jO S T A.cart B.cart z) : ℂ) + (omO S T w (jO S T A.cart B.cart z) : ℂ)) * Fw := by
    show Fd _ - Real.pi * Complex.I * (omO S T (a + w) _ : ℂ) * Fw = _
    rw [LinearMap.map_add, LinearMap.add_apply, Complex.ofReal_add]
  rw [e1, e2] at hL
  linear_combination (Complex.exp (-(Real.pi * Complex.I) * (omO S T a w : ℂ))) * hL

end GlobalTheory.HeisTranslCR
