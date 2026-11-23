import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqMultiDiff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HessianOfCombinationMetricLinear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialDetHermitianSumZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackChartMetricBlockFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernIntegralLinearRelationZeroStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FibreProj

theorem pol_archInt_pull_eq_zero : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d D : ℕ), GenSmooth q d → IsArithVar p D → ∀ (f : Y ⟶ B) (w : f ≫ q = p) (α β : Type) [Fintype α] [Fintype β], d < Fintype.card β → ∀ (L : α → HermLB p) (A : β → HermLB q) (M : HermLB p) (r : M.B.ι → Y.functionFieldˣ) (hr : IsRatSec M.B r), (∀ n, (comb (Sum.elim L fun a => (A a).pull f w) n).ArchIntegrable M D hr) → pol (fun n => (comb (Sum.elim L fun a => (A a).pull f w) n).archInt M D hr) = 0 := by
  classical
  intro k _ B Y _ q p d D hB hX f w α β _ _ hd L A M r hr hint
  set F : α ⊕ β → HermLB p := Sum.elim L fun a => (A a).pull f w with hF
  haveI := hX.finite_emb
  letI := Fintype.ofFinite (k →+* ℂ)
  simp only [HermLB.archInt, finsum_eq_sum_of_fintype]
  rw [pol_sum]
  refine Finset.sum_eq_zero fun σ _ => ?_
  unfold pol
  refine GlobalTheory.T.chern_integral_linear_relation_zero k Y p hX.isProjOver σ D (Finset (α ⊕ β)) _ _ ?_ _ _ fun S => hint _ σ
  intro c y hy
  obtain ⟨R⟩ := hB σ
  obtain ⟨i, hi⟩ := R.cover (PtsOver.map f w (spMap σ) y)
  obtain ⟨P, Q, hPQ⟩ := GlobalTheory.T.pullback_chart_metric_block_form k B Y q p f w σ D d c (R.chart i) y hy hi
  choose K hK using fun b => hPQ (A b) (pick (((A b).pull f w).φ σ).isLB y) (mem_pick _ y)
  set m : ∀ l, (F l).B.ι := fun l => pick ((F l).φ σ).isLB y with hm
  have hK' : ∀ b, c.hess ((F (Sum.inr b)).φ σ) (m (Sum.inr b)) y = P * K b * Q := hK
  have key : ∀ n : α ⊕ β → ℤ, c.chernDens ((comb F n).φ σ) y = D.factorial / Real.pi ^ D *
      (Matrix.det (∑ a, ((n (Sum.inl a) : ℝ) : ℂ) • c.hess ((F (Sum.inl a)).φ σ) (m (Sum.inl a)) y +
        ∑ b, ((n (Sum.inr b) : ℝ) : ℂ) • (P * K b * Q))).re := by
    intro n
    rw [AlgChart.chernDens, GlobalTheory.Mean4O.ReadsProj.hess_comb F n σ c hy _ (mem_pick _ y) m
      (fun l => mem_pick _ y), Fintype.sum_sum_type]
    simp only [hK']
  simp only [key]
  have h0 := pol_const_mul (D.factorial / Real.pi ^ D) (fun n : α ⊕ β → ℤ =>
      (Matrix.det (∑ a, ((n (Sum.inl a) : ℝ) : ℂ) • c.hess ((F (Sum.inl a)).φ σ) (m (Sum.inl a)) y +
        ∑ b, ((n (Sum.inr b) : ℝ) : ℂ) • (P * K b * Q))).re)
  rw [GlobalTheory.T.polynomial_det_hermitian_sum_zero D d α β hd, mul_zero] at h0
  unfold pol at h0
  exact h0

end GlobalTheory.FibreProj
