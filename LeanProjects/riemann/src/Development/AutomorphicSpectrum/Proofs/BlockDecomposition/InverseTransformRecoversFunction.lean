import Mathlib
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaussTubeOfTubeGood
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExponentialFourierIntegralBoundStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierInversionProdStatement

noncomputable section

open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier

namespace GlobalTheory.CompanionTheory.TubeFourier.PhiInv

theorem dot_pt_eq (x y t : ℝ × ℝ) :
    dot (pt x y) t = ((rdot x t : ℝ) : ℂ) + Complex.I * ((rdot y t : ℝ) : ℂ) := by
  apply Complex.ext <;> simp [dot, pt, rdot]

theorem integrable_gaussian_prod :
    Integrable (fun y : ℝ × ℝ => Real.exp (-(y.1 ^ 2 + y.2 ^ 2))) := by
  have h1 : Integrable (fun x : ℝ => Real.exp (-1 * x ^ 2)) := integrable_exp_neg_mul_sq one_pos
  have h2 := h1.mul_prod h1
  rw [← Measure.volume_eq_prod] at h2
  refine h2.congr (Eventually.of_forall fun y => ?_)
  simp only
  rw [← Real.exp_add]
  congr 1
  ring

theorem phi_eq_smul {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    (G : ℂ × ℂ → X) (x t : ℝ × ℝ) :
    phi G x t = Complex.exp (-((rdot x t : ℝ) : ℂ)) •
      ∫ y : ℝ × ℝ, Complex.exp (-(Complex.I * ((rdot y t : ℝ) : ℂ))) • G (pt x y) := by
  unfold phi
  rw [← integral_smul]
  congr 1
  funext y
  rw [smul_smul, dot_pt_eq, ← Complex.exp_add]
  congr 2
  ring

theorem hat_eq_smul {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    (G : ℂ × ℂ → X) (x t : ℝ × ℝ) :
    (∫ y : ℝ × ℝ, Complex.exp (-(Complex.I * ((rdot y t : ℝ) : ℂ))) • G (pt x y)) =
      Complex.exp ((rdot x t : ℝ) : ℂ) • phi G x t := by
  rw [phi_eq_smul, smul_smul, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_smul]

theorem inv_phi_eq : ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X] (G : ℂ × ℂ → X)
    (x : ℝ × ℝ), Continuous (fun y => G (pt x y)) →
    (∃ M : ℝ, ∀ y : ℝ × ℝ, ‖G (pt x y)‖ ≤ M * Real.exp (-(y.1 ^ 2 + y.2 ^ 2))) →
    Continuous (phi G x) →
    (∃ ε : ℝ, 0 < ε ∧ ∃ M : ℝ, ∀ t : ℝ × ℝ,
      ‖phi G x t‖ ≤ M * Real.exp (-rdot x t) * Real.exp (-ε * (|t.1| + |t.2|))) →
    ∀ y : ℝ × ℝ, inv (phi G x) (pt x y) = G (pt x y) := by
  intro X _ _ _ G x hc ⟨M, hM⟩ hphic ⟨ε, hε, M', hM'⟩ y
  have hint : Integrable (fun y : ℝ × ℝ => G (pt x y)) :=
    Integrable.mono' (integrable_gaussian_prod.const_mul M) hc.aestronglyMeasurable
      (Eventually.of_forall fun y => hM y)
  have hdx : ∀ t, dot (pt x 0) t = ((rdot x t : ℝ) : ℂ) := by
    intro t; rw [dot_pt_eq]; simp [rdot]
  have hl : ((pt x 0).1.re, (pt x 0).2.re) = x := by simp [pt]
  have hint2 : Integrable (fun t : ℝ × ℝ =>
      ∫ y : ℝ × ℝ, Complex.exp (-(Complex.I * ((rdot y t : ℝ) : ℂ))) • G (pt x y)) := by
    have h0 := (GlobalTheory.T.exponential_fourier_integral_bound X (phi G x) (pt x 0) ε M' hε hphic (by rw [hl]; exact hM')).1
    refine h0.congr (Eventually.of_forall fun t => ?_)
    show Complex.exp (dot (pt x 0) t) • phi G x t =
      ∫ y : ℝ × ℝ, Complex.exp (-(Complex.I * ((rdot y t : ℝ) : ℂ))) • G (pt x y)
    rw [hdx, hat_eq_smul]
  have key := GlobalTheory.T.fourier_inversion_real_plane X (fun y => G (pt x y)) hc hint hint2 y
  rw [key]
  unfold inv
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  beta_reduce
  rw [hat_eq_smul, smul_smul, dot_pt_eq, ← Complex.exp_add]
  congr 2
  ring

end GlobalTheory.CompanionTheory.TubeFourier.PhiInv
