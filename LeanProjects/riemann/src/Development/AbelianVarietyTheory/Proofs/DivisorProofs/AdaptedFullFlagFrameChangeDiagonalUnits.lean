import Development.AbelianVarietyTheory.Definitions.Divisors.IsMetricFrOfIsMetricOn
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.FlagChange

theorem diag_unitAt_and_mul : ∀ (F : Type) [Field F] (X : Var F) (ι : Type) (m : ι → ℕ) (E : Fr (ratOf X) m m) (B : Mat m X.Fn),
    B ∈ E.S (genericPoint X.X) → ∀ (z : X.X) (A A' : Mat m X.Fn), A ∈ E.S z → A' ∈ E.S z → ∀ x : Root m,
      UnitAt z ((A' * A⁻¹) x.1 x.2 x.2) ∧ (B * A⁻¹) x.1 x.2 x.2 = (B * A'⁻¹) x.1 x.2 x.2 * (A' * A⁻¹) x.1 x.2 x.2 := by
  intro F _ X ι m E B hB z A A' hA hA' x
  obtain ⟨τ, i⟩ := x
  have hP : Par m ((ratOf X).O z).toSubring (A' * A⁻¹) := (Fr.mem_iff hA).1 hA'
  have hl : ∀ (C : Mat m X.Fn) (O : Subring X.Fn), Par m O C → (C τ).BlockTriangular OrderDual.toDual := by
    intro C O hC a b hab
    exact (hC τ).2.2.2 a b a.2 hab
  refine ⟨?_, ?_⟩
  · set P := A' * A⁻¹ with hPdef
    have hdet : (P τ).det = P τ i i * ∏ j ∈ Finset.univ.erase i, P τ j j := by
      rw [Matrix.det_of_lowerTriangular _ (hl P _ hP),
        Finset.mul_prod_erase Finset.univ (fun j => P τ j j) (Finset.mem_univ i)]
    have hne : (P τ).det ≠ 0 := hP.det_ne τ
    rw [hdet] at hne
    have hii : P τ i i ≠ 0 := left_ne_zero_of_mul hne
    have hR : ∏ j ∈ Finset.univ.erase i, P τ j j ≠ 0 := right_ne_zero_of_mul hne
    have hmem : ∀ a b, P τ a b ∈ (ratOf X).O z := fun a b => (hP τ).1 a b
    have hinv : (P τ i i)⁻¹ ∈ (ratOf X).O z := by
      have e : (P τ i i)⁻¹ = (P τ).det⁻¹ * ∏ j ∈ Finset.univ.erase i, P τ j j := by
        rw [hdet, _root_.mul_inv, mul_assoc, inv_mul_cancel₀ hR, mul_one]
      rw [e]
      refine ((ratOf X).O z).mul_mem (hP τ).2.2.1 (((ratOf X).O z).prod_mem fun j _ => hmem j j)
    exact (unitAt_iff hii).2 ⟨mem_O_ratOf.1 (hmem i i), mem_O_ratOf.1 hinv⟩
  · have hA'g : A' ∈ E.S (genericPoint X.X) := Fr.mem_genericPoint hA'
    have hQ : Par m ((ratOf X).O (genericPoint X.X)).toSubring (B * A'⁻¹) := (Fr.mem_iff hA'g).1 hB
    have e : B * A⁻¹ = B * A'⁻¹ * (A' * A⁻¹) := by
      rw [mul_assoc, ← mul_assoc A'⁻¹, Mat.inv_mul (Fr.det_ne hA'), one_mul]
    rw [e]
    show ((B * A'⁻¹) τ * (A' * A⁻¹) τ) i i = _
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_single i (fun l _ hl' => ?_) (fun h => absurd (Finset.mem_univ i) h)
    rcases lt_or_gt_of_ne hl' with h | h
    · rw [(hP τ).2.2.2 l i l.2 h, mul_zero]
    · rw [(hQ τ).2.2.2 i l i.2 h, zero_mul]

end GlobalTheory.FlagChange
