import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroTypeInertia
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
open NumberField IsDedekindDomain Polynomial

namespace GlobalTheory

theorem valuation_pow_sub_pow_lt_one {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {a b : Ω}
    (ha : A.valuation a ≤ 1) (hb : A.valuation b ≤ 1) (hab : A.valuation (a - b) < 1) (k : ℕ) :
    A.valuation (a ^ k - b ^ k) < 1 := by
  rw [← Commute.geom_sum₂_mul (Commute.all a b), map_mul]
  have hs : A.valuation (∑ i ∈ Finset.range k, a ^ i * b ^ (k - 1 - i)) ≤ 1 := by
    apply Valuation.map_sum_le
    intro i _
    rw [map_mul, map_pow, map_pow]
    exact mul_le_one' (pow_le_one' ha _) (pow_le_one' hb _)
  exact lt_of_le_of_lt (mul_le_of_le_one_left' hs) hab

theorem frob_pow_apply_sub_lt_one :
    ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] (A : ValuationSubring Ω) (q : ℕ) (σ : Ω ≃ₐ[F] Ω),
    Formalism.ConjugateSelfDual.IsFrob A q σ → ∀ (n : ℕ) (x : Ω), A.valuation x ≤ 1 → A.valuation ((σ ^ n) x - x ^ (q ^ n)) < 1 := by
  intro F Ω _ _ _ _ A q σ hσ n
  obtain ⟨hD, hF⟩ := hσ
  have hD' : σ ∈ ReciprocityTheory.Gal.Dec (F := F) A := hD
  have hle : ∀ y : Ω, A.valuation y ≤ 1 → A.valuation (σ y) ≤ 1 := by
    intro y hy
    rw [A.valuation_le_one_iff] at hy ⊢
    exact (ReciprocityTheory.Gal.apply_mem_iff_of_mem_Dec hD' y).mpr hy
  induction n with
  | zero =>
    intro x _
    simp
  | succ n ih =>
    intro x hx
    have e : (σ ^ (n + 1)) x - x ^ (q ^ (n + 1)) =
        σ ((σ ^ n) x - x ^ (q ^ n)) + ((σ x) ^ (q ^ n) - (x ^ q) ^ (q ^ n)) := by
      rw [pow_succ' σ n, AlgEquiv.mul_apply, map_sub, map_pow, ← pow_mul, ← pow_succ']
      ring
    rw [e]
    refine Valuation.map_add_lt _ ?_ ?_
    · exact (ReciprocityTheory.Gal.valuation_apply_lt_one_iff hD' _).mpr (ih x hx)
    · refine valuation_pow_sub_pow_lt_one A (hle x hx) ?_ (hF x hx) _
      rw [map_pow]; exact pow_le_one' hx _

end GlobalTheory
