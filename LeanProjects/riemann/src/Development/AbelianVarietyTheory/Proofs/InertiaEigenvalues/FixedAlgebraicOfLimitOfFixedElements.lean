import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalLanglandsExists
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroCuspidalLL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalConverseGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInduction
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BrauerDegreeZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChevalleyUnits
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.FixApprox

theorem val_lt_map {K : Type} [Field K] (B : ValuationSubring K) (τ : K ≃+* K)
    (hB : ∀ z, τ z ∈ B ↔ z ∈ B) (a b : K) (h : B.valuation a < B.valuation b) :
    B.valuation (τ a) < B.valuation (τ b) := by
  have hb : b ≠ 0 := by
    rintro rfl; simp at h
  by_cases ha : a = 0
  · subst ha
    simp only [map_zero]
    exact (Valuation.pos_iff _).2 (by simpa using hb)
  · have hta : τ a ≠ 0 := by simpa using ha
    rw [← not_le] at h ⊢
    intro h'
    apply h
    have h1 : B.valuation (τ b / τ a) ≤ 1 := by
      rw [map_div₀, div_le_one₀ ((Valuation.pos_iff _).2 hta)]; exact h'
    rw [ValuationSubring.valuation_le_one_iff, ← map_div₀, hB] at h1
    rw [← ValuationSubring.valuation_le_one_iff, map_div₀, div_le_one₀ ((Valuation.pos_iff _).2 ha)] at h1
    exact h1

theorem fix_of_approx : ∀ (K : Type) [Field K] [CharZero K] (B : ValuationSubring K) (τ : K ≃+* K), (∀ z, τ z ∈ B ↔ z ∈ B) → ∀ y : K, IsAlgebraic ℚ y → (∀ δ : K, δ ≠ 0 → ∃ u : K, τ u = u ∧ B.valuation (y - u) < B.valuation δ) → τ y = y := by
  intro K _ _ B τ hB y _ happ
  by_contra hne
  set m := τ y with hm
  set s := τ.symm y with hs
  have hym : y - m ≠ 0 := sub_ne_zero.2 (Ne.symm hne)
  have hys : y - s ≠ 0 := by
    intro h
    apply hne
    have h' := congrArg τ (sub_eq_zero.1 h)
    rw [hs, RingEquiv.apply_symm_apply] at h'
    exact h'
  obtain ⟨u, hu, hlt⟩ := happ (if B.valuation (y - m) ≤ B.valuation (y - s) then y - m else y - s)
    (by split_ifs <;> assumption)
  have h1 : B.valuation (y - u) < B.valuation (y - m) := by
    split_ifs at hlt with hc
    · exact hlt
    · exact lt_of_lt_of_le hlt (le_of_lt (not_le.1 hc))
  have h2 : B.valuation (y - u) < B.valuation (y - s) := by
    split_ifs at hlt with hc
    · exact lt_of_lt_of_le hlt hc
    · exact hlt
  have h3 := val_lt_map B τ hB _ _ h2
  have e1 : τ (y - u) = m - u := by rw [map_sub, hu]
  have e2 : τ (y - s) = m - y := by rw [map_sub, hs, RingEquiv.apply_symm_apply]
  rw [e1, e2] at h3
  have h4 : B.valuation (m - y) = B.valuation (y - m) := Valuation.map_sub_swap _ _ _
  have h5 : m - y = (m - u) - (y - u) := by ring
  have h6 : B.valuation (m - y) < B.valuation (m - y) := by
    calc B.valuation (m - y) = B.valuation ((m - u) - (y - u)) := by rw [← h5]
      _ < B.valuation (m - y) := Valuation.map_sub_lt _ h3 (h4 ▸ h1)
  exact lt_irrefl _ h6

end GlobalTheory.FixApprox
