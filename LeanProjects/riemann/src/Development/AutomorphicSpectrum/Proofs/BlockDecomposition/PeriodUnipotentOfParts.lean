import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.UnipotentTateFunctionalEquation
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.FunctionalEquationGL2GL1Complex
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValMeasurableEmbedding
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegenerateTermsVanish

noncomputable section

open MeasureTheory Complex Ad3 Ad3.LR Ad3.LR.C

namespace GlobalTheory.CompanionTheory.PerUAssembled

def rtEquiv (g : GL (Fin 3) ℝ) : M23 ≃L[ℝ] M23 :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun X => Matrix.of.symm (Matrix.of X * (g : Matrix (Fin 3) (Fin 3) ℝ))
      map_add' := fun X Y => by
        have : Matrix.of (X + Y) = Matrix.of X + Matrix.of Y := rfl
        rw [this, Matrix.add_mul]
        rfl
      map_smul' := fun c X => by
        have : Matrix.of (c • X) = c • Matrix.of X := rfl
        rw [this, Matrix.smul_mul]
        rfl
      invFun := fun X => Matrix.of.symm (Matrix.of X * ((g⁻¹ : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ))
      left_inv := fun X => by
        simp [Matrix.mul_assoc]
      right_inv := fun X => by
        simp [Matrix.mul_assoc] }

theorem rtEquiv_apply (g : GL (Fin 3) ℝ) (X : M23) :
    rtEquiv g X = Matrix.of.symm (Matrix.of X * (g : Matrix (Fin 3) (Fin 3) ℝ)) := rfl

def rtS (g : GL (Fin 3) ℝ) (Φ : Sw) : Sw :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (rtEquiv g) Φ

theorem rtS_coe (g : GL (Fin 3) ℝ) (Φ : Sw) : (rtS g Φ : M23 → ℂ) = B.rt g Φ := by
  funext X
  simp [rtS, B.rt, rtEquiv_apply]

theorem schwartz_bounds (f : Sw) (n : ℕ) :
    ∃ C : ℝ, ∀ m ≤ n, ∀ X : M23, (1 + ‖X‖) ^ n * ‖iteratedFDeriv ℝ m f X‖ ≤ C :=
  ⟨2 ^ n * (Finset.Iic (n, n)).sup (fun m => SchwartzMap.seminorm ℂ m.1 m.2) f, fun m hm X =>
    SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (n, n)) le_rfl hm f X⟩

theorem ae_det_ne_zero : ∀ᵐ h : M22, (Matrix.of h).det ≠ 0 := by
  rw [ae_iff]
  have h : volume {h : M22 | (Matrix.of h).det = 0} = 0 := GlobalTheory.CompanionTheory.GodementNull.dNull
  simpa using h

theorem perU : UnipotentSubstitution → UnipotentJointIntegrability → UnipotentTateFunctionalEquation → PuBound → PerU := by
  intro h1 h2 h3 h4 k hk Φ δ s hs0 hs1 u
  obtain ⟨C, M, hb⟩ := h4 k hk Φ δ s hs0 hs1
  have hI := (hb u).1
  refine ⟨hI, ?_⟩
  let G : M22 → ℂ := fun h => Wm k (Matrix.of h)⁻¹ * sg (Matrix.of h).det *
    ((|(Matrix.of h).det| ^ (-(1 : ℝ) / 2) : ℝ) : ℂ)
  let Ψ : M23 → ℂ := B.rt (cyc u) Φ
  let F : ℝˣ → M22 → ℂ := fun t h => chR δ s t * sg t * (((|(t : ℝ)|)⁻¹ : ℝ) : ℂ) *
    (G h * B.innB Ψ h (t : ℝ)⁻¹)
  have hsm : ContDiff ℝ (⊤ : ℕ∞) Ψ := by
    have := (rtS (cyc u) Φ).smooth ⊤
    rw [rtS_coe] at this
    exact this
  have hbd : ∀ n : ℕ, ∃ C : ℝ, ∀ m ≤ n, ∀ X : M23, (1 + ‖X‖) ^ n * ‖iteratedFDeriv ℝ m Ψ X‖ ≤ C := by
    intro n
    have := schwartz_bounds (rtS (cyc u) Φ) n
    rw [rtS_coe] at this
    exact this
  have e1 : ∀ t : ℝˣ, sec k Φ (mm t u) * chR δ s t = ∫ h, F t h := by
    intro t
    simp only [F]
    rw [h1 k hk Φ t u, integral_const_mul]
    ring
  have e2 : ∫ t, (∫ h, F t h) ∂mulR = ∫ h, (∫ t, F t h ∂mulR) :=
    integral_integral_swap (h2 k hk Φ δ s hs0 hs1 u)
  have e3 : ∀ᵐ h : M22, ∫ t, F t h ∂mulR =
      cr (!δ) 0 (-1) * gT (!δ) s * ∫ x, pI k Φ δ s u (h, x) := by
    filter_upwards [ae_det_ne_zero] with h hdet
    have hF : ∀ t : ℝˣ, F t h = G h * (chR δ s t * sg t * (((|(t : ℝ)|)⁻¹ : ℝ) : ℂ) *
        B.innB Ψ h (t : ℝ)⁻¹) := fun t => by
      simp only [F]
      ring
    simp only [hF]
    rw [integral_const_mul, h3 Ψ δ s hs0 hs1 hsm hbd h hdet]
    have hp : ∀ x : Fin 2 → ℝ, pI k Φ δ s u (h, x) =
        G h * (cr (!δ) (s - 1) (x 1) * Ψ (Matrix.of.symm (Matrix.of h * blk x))) := fun x => by
      simp only [pI, G, Ψ, B.rt, Equiv.apply_symm_apply]
      ring
    simp only [hp]
    rw [integral_const_mul]
    ring
  calc ∫ t, sec k Φ (mm t u) * chR δ s t ∂mulR
      = ∫ t, (∫ h, F t h) ∂mulR := integral_congr_ae (Filter.Eventually.of_forall e1)
    _ = ∫ h, (∫ t, F t h ∂mulR) := e2
    _ = ∫ h : M22, cr (!δ) 0 (-1) * gT (!δ) s * ∫ x, pI k Φ δ s u (h, x) := integral_congr_ae e3
    _ = cr (!δ) 0 (-1) * gT (!δ) s * Pu k Φ δ s u := by
      rw [integral_const_mul, Pu, Measure.volume_eq_prod, integral_prod _ hI]

end GlobalTheory.CompanionTheory.PerUAssembled
