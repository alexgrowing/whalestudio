import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoices
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMean
import Formalism.SharpRestriction.Divisibility.LatticeTransfer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ErrorFunctionalCoefficientBoundedStatement
open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.WeightThresholdDefs Filter Topology Classical GlobalTheory.FlagPoly GlobalTheory.FlagAr GlobalTheory.Mean4

namespace GlobalTheory.Mean4

theorem tendsto_zero_of_monomials {σ : Type} (n : ℕ) (EE : ℕ → MvPolynomial σ ℝ →ₗ[ℝ] ℝ)
    (h : ∀ m : σ →₀ ℕ, m.degree = n → Tendsto (fun B => EE B (monomial m 1)) atTop (𝓝 0))
    (F : MvPolynomial σ ℝ) (hF : F.IsHomogeneous n) : Tendsto (fun B => EE B F) atTop (𝓝 0) := by
  have e : ∀ B, EE B F = ∑ m ∈ F.support, F.coeff m * EE B (monomial m 1) := by
    intro B
    conv_lhs => rw [F.as_sum]
    rw [map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← smul_eq_mul, ← map_smul, smul_monomial, smul_eq_mul, mul_one]
  simp only [e]
  have : Tendsto (fun B => ∑ m ∈ F.support, F.coeff m * EE B (monomial m 1)) atTop
      (𝓝 (∑ m ∈ F.support, F.coeff m * 0)) := by
    refine tendsto_finsetSum _ fun m hm => (h m ?_).const_mul _
    have := hF (mem_support_iff.mp hm)
    rw [Finsupp.degree_eq_weight_one]
    exact this
  simpa using this

theorem tendsto_log_div_nat (C : ℝ) : Tendsto (fun B : ℕ => C * Real.log B / B) atTop (𝓝 0) := by
  have h := (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop).const_mul C
  simpa [mul_div_assoc, Function.comp_def] using h

theorem shapeF_of_shapeC : ∀ (D : D7) (Y : ShimX D.what₂.Tau), ∀ (Φ : ℝ → Fn Y) (hh : Fn Y),
    ShapeC Φ hh → ShapeF Φ hh := by
  intro D Y Φ hh ⟨C, B₁, H⟩
  have key : ∀ B : ℕ, ∃ (a b : ℝ) (EE : Fn Y), B₁ ≤ B →
      (∀ m : (D.what₂.Tau × Fin Y.N) →₀ ℕ, m.degree = dimY Y + 1 → |EE (monomial m 1)| ≤ C * Real.log B / B) ∧
      ∀ F, Φ B F - Y.vol * (hh F - a * shAll Y F - b * totAll Y F) = EE F := by
    intro B
    by_cases hB : B₁ ≤ B
    · obtain ⟨al, be, E, -, hE, hΦ⟩ := H B hB
      obtain ⟨EE, h1, h2⟩ := GlobalTheory.T.error_functional_coefficient_bounded D.what₂.Tau Y.N Y.j (Φ B) hh Y.vol (C * Real.log B / B)
        (fun _ => al) (fun _ => be) E hE hΦ
      refine ⟨al - be, be, EE, fun _ => ⟨h1, fun F => ?_⟩⟩
      rw [h2 F, shAll, totAll, Finset.mul_sum, Finset.mul_sum]
      ring
    · exact ⟨0, 0, 0, fun h => absurd h hB⟩
  choose a b EE hEE using key
  refine ⟨a, b, fun F hF => ?_⟩
  have h0 := tendsto_zero_of_monomials (dimY Y + 1) EE (fun m hm => ?_) F hF
  · refine h0.congr' ?_
    filter_upwards [eventually_ge_atTop B₁] with B hB
    exact ((hEE B hB).2 F).symm
  · refine squeeze_zero_norm' ?_ (tendsto_log_div_nat C)
    filter_upwards [eventually_ge_atTop B₁] with B hB
    exact (hEE B hB).1 m hm

end GlobalTheory.Mean4
