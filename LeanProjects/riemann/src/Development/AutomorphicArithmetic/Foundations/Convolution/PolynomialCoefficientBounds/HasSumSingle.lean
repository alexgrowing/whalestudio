import Mathlib
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.AffineCharacterGenerators.Generators
import Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.PieceAdd

open MvPolynomial Filter Topology PositivityTheory.Rg.Fx

private theorem hasSum_comp {ι : Type} (p : MvPolynomial ι ℂ) (Λ : ι → ℂ) :
    HasSum (fun k => eval Λ (homogeneousComponent k p)) (eval Λ p) ∧
      Summable (fun k => ‖eval Λ (homogeneousComponent k p)‖) := by
  have h0 : ∀ k ∉ Finset.range (p.totalDegree + 1), eval Λ (homogeneousComponent k p) = 0 := by
    intro k hk
    rw [homogeneousComponent_eq_zero k p (by simpa using hk), map_zero]
  refine ⟨?_, summable_of_ne_finset_zero (s := Finset.range (p.totalDegree + 1))
    fun k hk => by rw [h0 k hk, norm_zero]⟩
  have h := hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional ℕ) h0
  rwa [← map_sum, sum_homogeneousComponent] at h

private theorem hasSum_single' {ι : Type} [Fintype ι] (v : ι → ℝ) (p : MvPolynomial ι ℂ) (Λ : ι → ℂ) :
    HasSum (fun k => ∑ b ∈ Finset.range (k + 1),
      ((b.factorial : ℂ)⁻¹ * eval Λ (lin v) ^ b) * eval Λ (homogeneousComponent (k - b) p))
      (Complex.exp (eval Λ (lin v)) * eval Λ p) := by
  obtain ⟨h1, h2⟩ := hasSum_comp p Λ
  set z := eval Λ (lin v)
  have e1 : HasSum (fun b : ℕ => (b.factorial : ℂ)⁻¹ * z ^ b) (Complex.exp z) := by
    rw [Complex.exp_eq_exp_ℂ]
    simpa [div_eq_inv_mul] using NormedSpace.expSeries_div_hasSum_exp z
  have e2 : Summable (fun b : ℕ => ‖(b.factorial : ℂ)⁻¹ * z ^ b‖) := e1.summable.norm
  have s := (summable_norm_sum_mul_range_of_summable_norm e2 h2).of_norm
  have t := tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm e2 h2
  rw [e1.tsum_eq, h1.tsum_eq] at t
  rw [t]
  exact s.hasSum

theorem UpperTheory.ConvolutionTheory.FX.piece_sum :
    ∀ (ι : Type) [Fintype ι] (f : EP ι) (Λ : ι → ℂ), HasSum (fun k => eval Λ (piece k f)) (ev Λ f) := by
  intro ι _ f Λ
  induction f using AddMonoidAlgebra.induction_linear with
  | zero =>
    simp only [fun k => (UpperTheory.ConvolutionTheory.FX.piece_add ι k).2.1, map_zero]
    exact hasSum_zero
  | add f g hf hg =>
    simp only [fun k => (UpperTheory.ConvolutionTheory.FX.piece_add ι k).1 f g, map_add]
    exact hf.add hg
  | single v p =>
    have hv : ev Λ (AddMonoidAlgebra.single v p : EP ι) = Complex.exp (eval Λ (lin v)) * eval Λ p := by
      simp [ev, PositivityTheory.Rg.Fx.lift, expChar, lin, mul_comm, aeval_eq_eval]
    rw [hv]
    convert hasSum_single' v p Λ using 2 with k
    rw [(UpperTheory.ConvolutionTheory.FX.piece_add ι k).2.2 v p, map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [map_mul, map_pow, eval_C]
    ring
