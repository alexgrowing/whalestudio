import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CentredSegments.IrreducibleUnif
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.TemperedProducts.CentredSegSqInt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.StandardFunctorsFiniteLength
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalizedAbsCharacterization
open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

namespace GlobalTheory.CompanionTheory.TopNilp

theorem nabs_absPow_of_tendsto_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (t : kˣ), Filter.Tendsto (fun n : ℕ => (t : k) ^ n) Filter.atTop (nhds 0) → 0 < nabs k t ∧ nabs k t < 1 ∧ ∀ d : ℕ, ‖((absPow k (d : ℂ) t : ℂˣ) : ℂ)‖ = nabs k t ^ d := by
  intro k _ _ _ _ t ht
  have hpos : 0 < nabs k t := nabs_pos' k t
  refine ⟨hpos, ?_, fun d => ?_⟩
  · by_contra hge
    have h1 : valuation k ((1 : kˣ) : k) ≤ valuation k (t : k) :=
      (nabs_le_iff 1 t).1 (by rw [nabs_one k]; exact not_lt.1 hge)
    rw [Units.val_one, map_one] at h1
    obtain ⟨r, hr, hr1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation k)
    have hr0 : r ≠ 0 := by simpa using hr
    have hnh : cball (Units.mk0 r hr0) ∈ 𝓝 (0 : k) :=
      (isOpen_cball _).mem_nhds (by simp [cball])
    obtain ⟨n, hn⟩ := (ht.eventually hnh).exists
    have h2 : valuation k ((t : k) ^ n) ≤ valuation k r := hn
    rw [map_pow] at h2
    exact absurd ((one_le_pow₀ h1).trans h2) (not_le.2 hr1)
  · rw [val_absPow, Complex.cpow_natCast, norm_pow, Complex.norm_real, Real.norm_of_nonneg hpos.le]

end GlobalTheory.CompanionTheory.TopNilp
