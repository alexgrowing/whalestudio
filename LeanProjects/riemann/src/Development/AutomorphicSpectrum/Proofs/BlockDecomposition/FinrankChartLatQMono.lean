import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsNefSectionsAsymptotic
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsShiftSectionBound
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsFujitaOne
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Imports
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.AmpleSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.NefRR
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry GroundTheory.Heights₂.Heights.HilbertSamuel Filter Topology

namespace GlobalTheory.CompanionTheory.ChartSections

theorem finrank_chartLatQ_mono : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (y : (Σ k, ι k) → Ω) (b b' : K → ℤ), (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → b ≤ b' →
    FiniteDimensional ℚ (chartLatQ y b' 1) →
    Module.finrank ℚ (chartLatQ y b 1) ≤ Module.finrank ℚ (chartLatQ y b' 1) := by
  intro K _ ι _ Ω _ _ y b b' hy hb hfd
  choose j hj using hy
  obtain ⟨n, hn⟩ : ∃ n : K → ℕ, ∀ k, (n k : ℤ) = b' k - b k :=
    ⟨fun k => (b' k - b k).toNat, fun k => Int.toNat_of_nonneg (sub_nonneg.2 (hb k))⟩
  have hu0 : (∏ k, y ⟨k, j k⟩ ^ n k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hj k)
  have hmem : ∀ s ∈ chartLatQ y b 1, s * ∏ k, y ⟨k, j k⟩ ^ n k ∈ chartLatQ y b' 1 := by
    intro s hs c hc
    have h1 : s * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * b k)) ∈ chartRingQ y c := hs c hc
    have hq : ∀ k, y ⟨k, j k⟩ / y ⟨k, c k⟩ ∈ chartRingQ y c :=
      fun k => Algebra.subset_adjoin ⟨⟨k, j k⟩, rfl⟩
    have h2 : ∏ k, (y ⟨k, j k⟩ / y ⟨k, c k⟩) ^ n k ∈ chartRingQ y c :=
      prod_mem fun k _ => pow_mem (hq k) _
    have heq : s * (∏ k, y ⟨k, j k⟩ ^ n k) * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * b' k)) =
        (s * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * b k))) * ∏ k, (y ⟨k, j k⟩ / y ⟨k, c k⟩) ^ n k := by
      rw [mul_assoc, mul_assoc, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      congr 1
      refine Finset.prod_congr rfl fun k _ => ?_
      have hck := hc k
      have hnk := hn k
      have hz : y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * b' k)) =
          y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * b k)) * (y ⟨k, c k⟩ ^ n k)⁻¹ := by
        rw [← zpow_natCast, ← zpow_neg, ← zpow_add₀ hck]
        congr 1
        simp only [Nat.cast_one, one_mul]
        omega
      rw [hz, div_pow, div_eq_mul_inv]
      ring
    show s * (∏ k, y ⟨k, j k⟩ ^ n k) * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * b' k)) ∈ chartRingQ y c
    rw [heq]
    exact mul_mem h1 h2
  let f : chartLatQ y b 1 →ₗ[ℚ] chartLatQ y b' 1 :=
    { toFun := fun s => ⟨s.1 * ∏ k, y ⟨k, j k⟩ ^ n k, hmem s.1 s.2⟩
      map_add' := fun s t => Subtype.ext (add_mul _ _ _)
      map_smul' := fun r s => Subtype.ext (smul_mul_assoc _ _ _) }
  refine LinearMap.finrank_le_finrank_of_injective (f := f) fun s t hst => ?_
  exact Subtype.ext (mul_right_cancel₀ hu0 (congrArg Subtype.val hst))

end GlobalTheory.CompanionTheory.ChartSections
