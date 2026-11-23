import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqCurve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical

namespace GlobalTheory.MixDens

theorem mix_eq_zero_of_re_form_eq_zero : ∀ (d : ℕ) (A M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ), A.IsHermitian → (∀ ξ : V (d + 1), (∑ j, ∑ l, ξ j * M j l * starRingEnd ℂ (ξ l)).re = 0) → mix d A M = 0 := by
  intro d A M hA hM
  have hf : ∀ f : Fin (d + 1) → ℂ, (∑ j, ∑ l, f j * M j l * starRingEnd ℂ (f l)).re = 0 := by
    intro f
    simpa using hM ((WithLp.equiv 2 (Fin (d + 1) → ℂ)).symm f)
  have hq : ∀ (a b : ℂ) (j l : Fin (d + 1)),
      (∑ k, ∑ m, (Pi.single j a + Pi.single l b : Fin (d + 1) → ℂ) k * M k m *
        starRingEnd ℂ ((Pi.single j a + Pi.single l b : Fin (d + 1) → ℂ) m)) =
      a * M j j * starRingEnd ℂ a + a * M j l * starRingEnd ℂ b + b * M l j * starRingEnd ℂ a
        + b * M l l * starRingEnd ℂ b := by
    intro a b j l
    simp only [Pi.add_apply, map_add, add_mul, mul_add, Finset.sum_add_distrib]
    simp [Pi.single_apply, apply_ite (starRingEnd ℂ), mul_ite, ite_mul, Finset.sum_ite_eq', Finset.sum_ite_eq]
    ring
  have h0 : ∀ j, (M j j).re = 0 := by
    intro j
    have := hf (Pi.single j 1 + Pi.single j 0)
    rw [hq] at this
    simpa using this
  have hskew : Mᴴ = -M := by
    ext j l
    have h1 := hf (Pi.single j 1 + Pi.single l 1)
    have h2 := hf (Pi.single j 1 + Pi.single l Complex.I)
    rw [hq] at h1 h2
    simp [Complex.mul_re, Complex.conj_re, Complex.conj_im, h0 j, h0 l] at h1 h2
    apply Complex.ext <;> simp [Matrix.conjTranspose_apply] <;> linarith
  have hH : A.adjugateᴴ = A.adjugate := by
    rw [adjugate_conjTranspose, hA.eq]
  have ht : starRingEnd ℂ (A.adjugate * M).trace = -(A.adjugate * M).trace := by
    rw [← Complex.star_def, ← Matrix.trace_conjTranspose, conjTranspose_mul, hH, hskew, Matrix.neg_mul, trace_neg, trace_mul_comm]
  have hre : (A.adjugate * M).trace.re = 0 := by
    have := congrArg Complex.re ht
    simp at this
    linarith
  rw [mix, hre, mul_zero]

end GlobalTheory.MixDens
