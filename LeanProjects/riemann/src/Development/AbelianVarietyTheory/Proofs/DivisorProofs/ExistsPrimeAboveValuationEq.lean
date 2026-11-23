import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPlaceRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDifferentExponentDenominator
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct

noncomputable section

namespace GlobalTheory.CNumAtPrime

theorem cNum_eq_c_vp : ∀ (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] (𝔣 : Ideal (OF E)) (l : ℕ), l.Prime →
    ∃ P : HeightOneSpectrum (𝓞 E), (l : 𝓞 E) ∈ P.asIdeal ∧ ((GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.cNum_vp 𝔣 l P : ℚ) : ℝ) = c_vp 𝔣 l := by
  intro E _ _ _ 𝔣 l hl
  classical
  have hlu : ¬ IsUnit (l : 𝓞 E) := by
    intro h
    have h2 := h.map (Algebra.norm ℤ (S := 𝓞 E))
    rw [show (l : 𝓞 E) = algebraMap ℤ (𝓞 E) (l : ℤ) by simp, Algebra.norm_algebraMap] at h2
    have hn : Module.finrank ℤ (𝓞 E) ≠ 0 := Module.finrank_pos.ne'
    rw [isUnit_pow_iff hn, Int.isUnit_iff] at h2
    have := hl.one_lt
    omega
  obtain ⟨M, hM, hlM⟩ := Ideal.exists_le_maximal _ ((Ideal.span_singleton_ne_top hlu))
  have hlP : (l : 𝓞 E) ∈ M := hlM (Ideal.mem_span_singleton_self _)
  have hM0 : M ≠ ⊥ := by
    rintro rfl
    exact Nat.cast_ne_zero.2 hl.ne_zero ((Submodule.mem_bot _).1 hlP)
  let P : HeightOneSpectrum (𝓞 E) := ⟨M, hM.isPrime, hM0⟩
  refine ⟨P, hlP, ?_⟩
  have hiff : (∃ v : HeightOneSpectrum (OF E), v.asIdeal ∣ 𝔣 ∧ (l : OF E) ∈ v.asIdeal) ↔
      (∃ v : HeightOneSpectrum (OF E), (l : OF E) ∈ v.asIdeal ∧ v.asIdeal ∣ 𝔣) :=
    ⟨fun ⟨v, a, b⟩ => ⟨v, b, a⟩, fun ⟨v, a, b⟩ => ⟨v, b, a⟩⟩
  unfold GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.cNum_vp c_vp
  by_cases h : ∃ v : HeightOneSpectrum (OF E), v.asIdeal ∣ 𝔣 ∧ (l : OF E) ∈ v.asIdeal
  · rw [if_pos h, if_pos (hiff.1 h)]
    have hc : GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.condExp 𝔣 l = a0 𝔣 l := by
      unfold GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.condExp a0
      congr 1
    rw [hc]
    push_cast
    rfl
  · rw [if_neg h, if_neg (mt hiff.2 h)]
    unfold GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.diffExp_vp GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.delta_vp
    rw [GlobalTheory.DifferentElement.mult_ratio E l hl P.asIdeal P.isPrime hlP,
      show padicValInt l (discr E) = padicValNat l (discr E).natAbs from rfl, Nat.factorization_def _ hl]
    push_cast
    rfl

end GlobalTheory.CNumAtPrime
