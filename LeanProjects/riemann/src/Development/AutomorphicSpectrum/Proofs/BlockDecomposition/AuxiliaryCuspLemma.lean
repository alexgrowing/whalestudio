import Mathlib
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsingletonRankZero
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AutomorphicSpectrum.PublishedTheorems.PublishedGlobalResults.HasInfCharOfIsRegAlg
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ClozelCohomologicalModel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DiscreteSpectrumGLTwoOfCuspidalSpectrum
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ClozelPurity.EopV
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieCentralElementTraceStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TraceOperatorEigenvalueSumStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralEigenExponentialStatement

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL MeasureTheory PositivityTheory.S2.Clozel

namespace GlobalTheory.CompanionTheory.Clozel

theorem exists_twist_isNormalised : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a →
    ∀ π : CuspSub E a, (∀ τ : E →+* ℂ, ∃ m, π.HasInfChar τ m) →
    ∃ s : ℂ, GlobalTheory.DiscSpec.IsNormalised (π.twist (GlobalTheory.CuspRep.Model.absC E s)) := by
  intro E _ _ _ a ha π hm
  choose m hm using hm
  have hN : (Fintype.card (E →+* ℂ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have ha' : (a : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  refine ⟨-(∑ τ, (m τ).sum) / (a * Fintype.card (E →+* ℂ)), ?_⟩
  set s : ℂ := -(∑ τ, (m τ).sum) / (a * Fintype.card (E →+* ℂ)) with hs
  intro φ hφ t g
  have hsum : ∀ τ : E →+* ℂ, (∑ i : Fin a, Eop τ i i) φ = ((m τ).sum + a * s) • φ := fun τ => by
    have h1 := (hm τ).twist (GlobalTheory.CuspRep.Model.absC E s)
    rw [GlobalTheory.CuspRep.Model.expo_absC] at h1
    rw [GlobalTheory.T.trace_operator_eigenvalue_sum E a _ τ _ h1 φ hφ, Multiset.sum_map_add]
    simp [(hm τ).1]
  have hc : ∑ τ : E →+* ℂ, ((m τ).sum + a * s) = 0 := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hs]
    field_simp
    ring
  have hlie : lie E a (oneL E a) φ = (0 : ℂ) • φ := by
    rw [GlobalTheory.T.lie_central_element_trace E a, LinearMap.sum_apply, Finset.sum_congr rfl fun τ _ => hsum τ, ← Finset.sum_smul, hc]
  simpa using GlobalTheory.T.central_eigen_exponential E a φ 0 hlie t g

end GlobalTheory.CompanionTheory.Clozel
