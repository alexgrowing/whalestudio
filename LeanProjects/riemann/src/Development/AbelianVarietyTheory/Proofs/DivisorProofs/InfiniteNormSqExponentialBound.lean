import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfSqNormEqExpGapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ApproxGapLeConstMul

open NumberField IsDedekindDomain Filter Topology
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovHt.Link GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.Cartier GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal

namespace GlobalTheory.CovHt.Link

theorem hodge_le_exp_nrmInf : Hypotheses2 → HypothesesH → RegSt → ∀ (D : D7) (O : Setup D) (x : ToroidalCompactificationData O.s) (P : Mean4O.PolOf x O.Φ), O.CoreWith x P → 2 < D.R.f * (O.N - 1) → ∀ u : AllWt.Weight O.S.Dw, (∀ τ, StrictAnti (u τ)) → ∀ B : ℝ, 2 ≤ B → ∀ k : O.s.Comp, ∃ C : ℝ, ∀ᶠ r : ℚ in 𝓝[>] 0, ∀ τ : ℕ, 1 ≤ τ → ∀ f ∈ (mbarOf P B (wtR O.L u) r k).secs τ, ∀ (σ : D.what₂.LL →+* ℂ), ∀ y ∈ offBd O.Φ k σ, infSq O.Φ k x (τ • u) σ f y ≤ (Real.exp (C * r * τ) * (mbarOf P B (wtR O.L u) r k).nrmInf σ τ f y) ^ 2 := by
  intro h2 hH hR D O x P hc hdim u hu B hB k
  obtain ⟨C, hC⟩ := GlobalTheory.T.approx_gap_le_const_mul h2 hH hR D O x P hc hdim u hu B hB k
  refine ⟨C, ?_⟩
  filter_upwards [hC, self_mem_nhdsWithin] with r hr hr0
  intro τ hτ f hf σ y hy
  rw [GlobalTheory.T.inf_sq_norm_eq_exp_gap D O.A O.N O.j O.S O.κ O.s O.Φ O.L x P B u r hr0 k τ hτ f hf σ y hy]
  have h1 := hr σ y hy
  have h0 : (0:ℝ) ≤ τ := by positivity
  have h3 : 2 * (τ:ℝ) * apxGap O.Φ O.L x P B u r k σ y ≤ 2 * (C * r * τ) := by nlinarith
  calc _ ≤ (mbarOf P B (wtR O.L u) r k).nrmInf σ τ f y ^ 2 * Real.exp (2 * (C * r * τ)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 h3) (sq_nonneg _)
    _ = _ := by rw [mul_pow, ← Real.exp_nat_mul]; push_cast; ring_nf

end GlobalTheory.CovHt.Link
