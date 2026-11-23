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

theorem finrank_chartLatQ_shift_le : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (y : (Σ k, ι k) → Ω) (b : K → ℤ) (e : K → ℕ) (M : ℕ), (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → (∀ k, e k ≤ M) →
    FiniteDimensional ℚ (chartLatQ y (b + fun _ => (M : ℤ)) 1) →
    Module.finrank ℚ (chartLatQ y (b + fun k => (e k : ℤ)) 1) ≤
      Module.finrank ℚ (chartLatQ y (b + fun _ => (M : ℤ)) 1) := by
  intro K _ ι _ Ω _ _ y b e M hy he hfd
  choose j hj using hy
  have hu0 : (∏ k, y ⟨k, j k⟩ ^ (M - e k)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hj k)
  have hmem : ∀ s ∈ chartLatQ y (b + fun k => (e k : ℤ)) 1,
      s * ∏ k, y ⟨k, j k⟩ ^ (M - e k) ∈ chartLatQ y (b + fun _ => (M : ℤ)) 1 := by
    intro s hs c hc
    have h1 : s * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * (b + fun k => (e k : ℤ) : K → ℤ) k)) ∈ chartRingQ y c := hs c hc
    have hq : ∀ k, y ⟨k, j k⟩ / y ⟨k, c k⟩ ∈ chartRingQ y c :=
      fun k => Algebra.subset_adjoin ⟨⟨k, j k⟩, rfl⟩
    have h2 : ∏ k, (y ⟨k, j k⟩ / y ⟨k, c k⟩) ^ (M - e k) ∈ chartRingQ y c :=
      prod_mem fun k _ => pow_mem (hq k) _
    have heq : s * (∏ k, y ⟨k, j k⟩ ^ (M - e k)) *
          ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * (b + fun _ => (M : ℤ) : K → ℤ) k)) =
        (s * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * (b + fun k => (e k : ℤ) : K → ℤ) k))) *
          ∏ k, (y ⟨k, j k⟩ / y ⟨k, c k⟩) ^ (M - e k) := by
      rw [mul_assoc, mul_assoc, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      congr 1
      refine Finset.prod_congr rfl fun k _ => ?_
      have hck := hc k
      have hek := he k
      have hz : y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * (b + fun _ => (M : ℤ) : K → ℤ) k)) =
          y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * (b + fun k => (e k : ℤ) : K → ℤ) k)) * (y ⟨k, c k⟩ ^ (M - e k))⁻¹ := by
        rw [← zpow_natCast, ← zpow_neg, ← zpow_add₀ hck]
        congr 1
        simp only [Pi.add_apply, Nat.cast_one, one_mul]
        omega
      rw [hz, div_pow, div_eq_mul_inv]
      ring
    show s * (∏ k, y ⟨k, j k⟩ ^ (M - e k)) *
      ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * (b + fun _ => (M : ℤ) : K → ℤ) k)) ∈ chartRingQ y c
    rw [heq]
    exact mul_mem h1 h2
  let f : chartLatQ y (b + fun k => (e k : ℤ)) 1 →ₗ[ℚ] chartLatQ y (b + fun _ => (M : ℤ)) 1 :=
    { toFun := fun s => ⟨s.1 * ∏ k, y ⟨k, j k⟩ ^ (M - e k), hmem s.1 s.2⟩
      map_add' := fun s t => Subtype.ext (add_mul _ _ _)
      map_smul' := fun r s => Subtype.ext (smul_mul_assoc _ _ _) }
  refine LinearMap.finrank_le_finrank_of_injective (f := f) fun s t hst => ?_
  exact Subtype.ext (mul_right_cancel₀ hu0 (congrArg Subtype.val hst))

end GlobalTheory.CompanionTheory.ChartSections
