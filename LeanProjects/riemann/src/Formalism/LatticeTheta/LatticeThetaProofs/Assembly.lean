import Formalism.LatticeTheta.LatticeSummableDecay

open MeasureTheory Filter Asymptotics Complex
open scoped FourierTransform RealInnerProductSpace SchwartzMap

noncomputable section

namespace Formalism.H

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

lemma norm_exp_two_pi_I_mul (r : ℝ) : ‖Complex.exp (2 * Real.pi * Complex.I * (r : ℂ))‖ = 1 := by
  rw [show (2 * Real.pi * Complex.I * (r : ℂ)) = ((2 * Real.pi * r : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

theorem poissonDecay_of (hD : DualIsLattice V) (h1 : LatticeSummableDecay V)
    (h2 : Periodization V) (h3 : UnfoldCoeff V) (h4 : LatticeFourierSeries V) : PoissonDecay V := by
  intro Λ _ _ f hf b hb hfO hFO x
  obtain ⟨hdd, hdz⟩ := hD Λ
  haveI := hdd
  haveI : IsZLattice ℝ (dual Λ) := hdz

  have hphase : (fun v : V => (𝓕 f : V → ℂ) v * Complex.exp (2 * Real.pi * Complex.I * (⟪v, x⟫ : ℝ)))
      =O[cocompact V] (fun v => ‖v‖ ^ (-b)) := by
    refine (Asymptotics.IsBigO.of_bound 1 (Filter.Eventually.of_forall fun v => ?_)).trans hFO
    rw [norm_mul, norm_exp_two_pi_I_mul, mul_one, one_mul]
  have hsum := h1 (dual Λ) _ b hb hphase
  refine ⟨hsum, ?_⟩
  obtain ⟨hint, hper, hcont, hinv⟩ := h2 Λ f hf b hb hfO

  let B := Module.Free.chooseBasis ℤ Λ
  have hD' := ZLattice.isAddFundamentalDomain B (volume : Measure V)
  have hcoef : ∀ μ : dual Λ,
      ∫ y in ZSpan.fundamentalDomain (B.ofZLatticeBasis ℝ Λ), (∑' l : Λ, f ((l : V) + y)) *
        Complex.exp (-(2 * Real.pi * Complex.I * (⟪(μ : V), y⟫ : ℝ))) = (𝓕 f : V → ℂ) μ :=
    fun μ => h3 Λ f hint _ hD' μ μ.2
  have hFs : Summable (fun μ : dual Λ => (𝓕 f : V → ℂ) μ) := h1 (dual Λ) _ b hb hFO
  have hG := h4 Λ (fun y => ∑' l : Λ, f ((l : V) + y)) hcont
    (fun l y => by simpa using hinv l y) _ hD' (by simpa only [hcoef] using hFs) x
  simp only [hcoef] at hG
  have hval : (ZLattice.covolume Λ : ℂ)⁻¹ * ∑' μ : dual Λ, (𝓕 f : V → ℂ) μ *
      Complex.exp (2 * Real.pi * Complex.I * (⟪(μ : V), x⟫ : ℝ)) = ∑' l : Λ, f ((l : V) + x) := by
    rw [← tsum_mul_left, ← hG.tsum_eq]
    congr 1; funext μ; ring
  rw [hval]
  exact (hper x).hasSum

theorem poissonSchwartz_of (hP : PoissonDecay V) (h6 : SchwartzDecay V) : PoissonSchwartz V := by
  intro Λ _ _ f x
  have hd : (Module.finrank ℝ V : ℝ) < Module.finrank ℝ V + 1 := by linarith
  exact hP Λ f f.continuous _ hd (h6 f _).1 (h6 f _).2 x

theorem thetaSummable_of (h2 : Periodization V) (h5 : GaussFourier V) : ThetaSummable V := by
  intro Λ _ _ t ht x
  obtain ⟨hc, hO, -⟩ := h5 t ht
  have hd : (Module.finrank ℝ V : ℝ) < Module.finrank ℝ V + 1 := by linarith
  obtain ⟨-, hs, -⟩ := h2 Λ _ hc _ hd (hO _)
  exact Complex.summable_ofReal.1 (hs x)

theorem thetaPos_of (hS : ThetaSummable V) : ThetaPos V := by
  intro Λ _ _ t ht
  have hs := hS Λ t ht 0
  simp only [add_zero] at hs
  have := hs.le_tsum 0 (fun j _ => (Real.exp_pos _).le)
  simpa [theta] using this

theorem thetaShiftInversion_of (hP : PoissonDecay V) (h2 : Periodization V) (h5 : GaussFourier V) :
    ThetaShiftInversion V := by
  intro Λ _ _ t ht x
  obtain ⟨hc, hO, hF⟩ := h5 t ht
  have hd : (Module.finrank ℝ V : ℝ) < Module.finrank ℝ V + 1 := by linarith
  obtain ⟨hsum, hhas⟩ := hP Λ _ hc _ hd (hO _) (by
    have hO2 := (hO (Module.finrank ℝ V + 1))

    have hfun : (𝓕 (fun v : V => (Real.exp (-Real.pi * t * ‖v‖ ^ 2) : ℂ)) : V → ℂ) =
        fun w => ((t ^ (-(Module.finrank ℝ V : ℝ) / 2) : ℝ) : ℂ) * (Real.exp (-Real.pi * ‖w‖ ^ 2 / t) : ℂ) :=
      funext hF
    obtain ⟨-, hO', -⟩ := h5 (1 / t) (by positivity)
    rw [hfun]
    refine ((hO' (Module.finrank ℝ V + 1)).congr_left fun w => ?_).const_mul_left _
    congr 2
    field_simp) x
  simp only [hF] at hsum hhas
  set c : ℂ := ((t ^ (-(Module.finrank ℝ V : ℝ) / 2) : ℝ) : ℂ)
  have hc0 : c ≠ 0 := by
    simp only [c, ne_eq, Complex.ofReal_eq_zero]; exact (Real.rpow_pos_of_pos ht _).ne'
  have hsum' : Summable (fun μ : dual Λ => (Real.exp (-Real.pi * ‖(μ : V)‖ ^ 2 / t) : ℂ) *
      Complex.exp (2 * Real.pi * Complex.I * (⟪(μ : V), x⟫ : ℝ))) := by
    refine (hsum.mul_left c⁻¹).congr fun μ => ?_
    field_simp
  refine ⟨hsum', ?_⟩
  rw [thetaShift, Complex.ofReal_tsum, hhas.tsum_eq]
  have : (fun μ : dual Λ => c * (Real.exp (-Real.pi * ‖(μ : V)‖ ^ 2 / t) : ℂ) *
      Complex.exp (2 * Real.pi * Complex.I * (⟪(μ : V), x⟫ : ℝ))) =
      fun μ : dual Λ => c * ((Real.exp (-Real.pi * ‖(μ : V)‖ ^ 2 / t) : ℂ) *
      Complex.exp (2 * Real.pi * Complex.I * (⟪(μ : V), x⟫ : ℝ))) := by
    funext μ; ring
  rw [this, tsum_mul_left]
  ring

theorem thetaInversion_of (hS : ThetaShiftInversion V) : ThetaInversion V := by
  intro Λ _ _ t ht
  obtain ⟨-, h⟩ := hS Λ (1 / t) (by positivity) 0
  have hl : thetaShift Λ (1 / t) 0 = theta Λ (1 / t) := by
    simp [thetaShift, theta]
  rw [hl] at h
  have hr : ∀ μ : dual Λ, (Real.exp (-Real.pi * ‖(μ : V)‖ ^ 2 / (1 / t)) : ℂ) *
      Complex.exp (2 * Real.pi * Complex.I * (⟪(μ : V), (0 : V)⟫ : ℝ)) =
      ((Real.exp (-Real.pi * t * ‖(μ : V)‖ ^ 2) : ℝ) : ℂ) := by
    intro μ
    rw [inner_zero_right, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one]
    congr 2
    field_simp
  simp only [hr] at h
  rw [← Complex.ofReal_tsum] at h
  have hpow : (1 / t) ^ (-(Module.finrank ℝ V : ℝ) / 2) = t ^ ((Module.finrank ℝ V : ℝ) / 2) := by
    rw [one_div, Real.inv_rpow ht.le, neg_div, Real.rpow_neg ht.le, inv_inv]
  rw [hpow] at h
  have h' : (theta Λ (1 / t) : ℂ) = (((ZLattice.covolume Λ)⁻¹ * t ^ ((Module.finrank ℝ V : ℝ) / 2) *
      theta (dual Λ) t : ℝ) : ℂ) := by
    rw [h, theta]; push_cast; ring
  exact_mod_cast h'

end Formalism.H
