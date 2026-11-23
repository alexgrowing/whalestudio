import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPlaceRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SzPeriodsOfTangent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyOfForall

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LatModel

theorem norm_ratCast_padicComplex_le_one (l : ℕ) [Fact l.Prime] (q : ℚ) (hq : 0 ≤ padicValRat l q) :
    ‖(q : ℂ_[l])‖ ≤ 1 := by
  have e : ((q : ℚ_[l]) : ℂ_[l]) = (q : ℂ_[l]) := by
    exact map_ratCast (algebraMap ℚ_[l] ℂ_[l]) q
  rw [← e, PadicComplex.norm_extends', Padic.eq_padicNorm]
  by_cases h0 : q = 0
  · subst h0; simp
  · rw [padicNorm.eq_zpow_of_nonzero h0]
    have hl : (1 : ℚ) ≤ l := by exact_mod_cast (Fact.out : l.Prime).one_lt.le
    exact_mod_cast zpow_le_one_of_nonpos₀ hl (by omega)

theorem eventually_isPlaceRing (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime]
    (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) : Eventually l lam (IsPlaceRing E l lam) := by
  classical
  let t : (E →+* ℂ) → IntermediateField ℚ ℂ := fun σ ↦ σ.toRatAlgHom.fieldRange
  haveI : ∀ σ, FiniteDimensional ℚ (t σ) := fun σ ↦
    LinearEquiv.finiteDimensional (AlgEquiv.ofInjectiveField σ.toRatAlgHom).toLinearEquiv
  refine ⟨⨆ σ, t σ, IntermediateField.finiteDimensional_iSup_of_finite, fun R hR ↦ ?_⟩
  obtain ⟨hdvr, hsz, hmem⟩ := hR
  refine ⟨hdvr, hsz, fun q hq ↦ ?_, fun σ x ↦ ?_⟩
  · have hk : (q : ℂ) ∈ ⨆ σ, t σ := by
      simpa using IntermediateField.algebraMap_mem (⨆ σ, t σ) q
    have hqa : (q : ℂ) ∈ algebraicClosure ℚ ℂ := by
      simpa using (algebraicClosure ℚ ℂ).algebraMap_mem q
    refine hmem _ hk ⟨hqa, ?_⟩
    have e : (⟨(q : ℂ), hqa⟩ : algebraicClosure ℚ ℂ) = (q : algebraicClosure ℚ ℂ) := by
      ext; simp
    rw [e, map_ratCast, Real.rpow_zero]
    exact norm_ratCast_padicComplex_le_one l q hq
  · have hk : σ x ∈ ⨆ σ, t σ :=
      (le_iSup t σ) (AlgHom.mem_fieldRange.2 ⟨x, rfl⟩)
    have ha : σ x ∈ algebraicClosure ℚ ℂ :=
      mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom σ.toRatAlgHom)
    by_cases hn : ‖lam ⟨σ x, ha⟩‖ ≤ 1
    · refine ⟨σ x, hmem _ hk ⟨ha, by rwa [Real.rpow_zero]⟩, 1, R.one_mem, one_ne_zero, mul_one _⟩
    · push_neg at hn
      have h0 : σ x ≠ 0 := by
        intro h
        have : (⟨σ x, ha⟩ : algebraicClosure ℚ ℂ) = 0 := Subtype.ext h
        rw [this, map_zero, norm_zero] at hn
        linarith
      have hia : (σ x)⁻¹ ∈ algebraicClosure ℚ ℂ := inv_mem ha
      have hik : (σ x)⁻¹ ∈ ⨆ σ, t σ := inv_mem hk
      have e : (⟨(σ x)⁻¹, hia⟩ : algebraicClosure ℚ ℂ) = (⟨σ x, ha⟩ : algebraicClosure ℚ ℂ)⁻¹ := by
        ext; simp
      have hs : Sz l lam 0 (σ x)⁻¹ := by
        refine ⟨hia, ?_⟩
        rw [e, map_inv₀, norm_inv, Real.rpow_zero]
        exact inv_le_one_of_one_le₀ hn.le
      exact ⟨1, R.one_mem, (σ x)⁻¹, hmem _ hik hs, inv_ne_zero h0, mul_inv_cancel₀ h0⟩

end GlobalTheory.LatModel

example : ∀ (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]),
    GlobalTheory.LatModel.Eventually l lam (GlobalTheory.LatModel.IsPlaceRing E l lam) := GlobalTheory.LatModel.eventually_isPlaceRing
