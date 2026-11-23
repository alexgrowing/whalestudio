import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HypOneZeroZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalGramFibreMeasureUnramified
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

namespace GlobalTheory.CompanionTheory.WeilSiegel.Free.FibreBound

theorem compactOpen_mass_le : ∀ (V K : Type) [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V] [T2Space V] [TopologicalSpace K] [MeasurableSpace K] [BorelSpace K] [T2Space K] (μ : Measure V) (lam : Measure K) (Q : V → K) (Z : Set V) (m : K → Measure V), Continuous Q → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ Q id Z lam Set.univ m → ∀ P : Set V, IsCompact P → IsOpen P → P ⊆ Z → ∃ c : ℝ≥0, ∀ S : Set K, MeasurableSet S → μ (P ∩ Q ⁻¹' S) ≤ (c : ℝ≥0∞) * lam S := by
  intro V K _ _ _ _ _ _ _ _ μ lam Q Z m hQ h P hPc hPo hPZ
  have hPm : MeasurableSet P := hPo.measurableSet
  let φ : V → ℝ := P.indicator fun _ => 1
  have hφc : Continuous φ := by
    refine continuous_indicator ?_ continuous_const.continuousOn
    simp [hPo.frontier_eq, hPc.isClosed.closure_eq]
  have hφs : HasCompactSupport φ := by
    refine HasCompactSupport.intro hPc fun x hx => ?_
    exact Set.indicator_of_notMem hx _
  have hts : tsupport φ ⊆ Z := by
    refine subset_trans (closure_minimal (fun x hx => ?_) hPc.isClosed) hPZ
    by_contra h
    exact hx (Set.indicator_of_notMem h _)
  obtain ⟨hI, hC⟩ := h.2.2 φ hφc hφs hts
  have hint : ∀ s, ∫ x, φ x ∂(m s) = (m s P).toReal := fun s => by
    simp [φ, integral_indicator hPm, Measure.real]
  have hfin : ∀ s, m s P ≠ ⊤ := fun s => by
    have h := hI s (Set.mem_univ s)
    rw [integrable_indicator_iff hPm] at h
    rcases (integrableOn_const_iff (C := (1 : ℝ)) (by simp)).1 h with h | h
    · simp at h
    · exact h.ne
  have hcont : ContinuousOn (fun s => (m s P).toReal) (Q '' P) := by
    have h' : ContinuousOn (fun s => (m s P).toReal) Set.univ := by
      simpa only [hint] using hC
    exact h'.mono (Set.subset_univ _)
  obtain ⟨C, hCb⟩ := (hPc.image hQ).exists_bound_of_continuousOn hcont
  have hoff : ∀ s, s ∉ Q '' P → m s P = 0 := fun s hs => by
    have hae := GlobalTheory.CompanionTheory.SiegelND.Coef.AvgV.ae_lift_eq h (g := Q) (fun _ => rfl) Function.injective_id s
    refine measure_mono_null (t := {x | ¬ Q x = s}) ?_ hae
    intro x hx hxs
    exact hs ⟨x, hx, hxs⟩
  have hbd : ∀ s, m s P ≤ (C.toNNReal : ℝ≥0∞) := fun s => by
    by_cases hs : s ∈ Q '' P
    · have h1 : (m s P).toReal ≤ C := le_trans (le_abs_self _) (by simpa using hCb s hs)
      rw [← ENNReal.ofReal_toReal (hfin s)]
      exact ENNReal.ofReal_le_ofReal h1
    · rw [hoff s hs]
      exact bot_le
  refine ⟨C.toNNReal, fun S hS => ?_⟩
  rw [GlobalTheory.CompanionTheory.SiegelND.Coef.AvgV.fibre_mass_on h (g := Q) (fun _ => rfl) Function.injective_id hQ.measurable hPm hS
    (fun x hx => hPZ hx.1)]
  calc ∫⁻ s in S, m s P ∂lam ≤ ∫⁻ _ in S, (C.toNNReal : ℝ≥0∞) ∂lam := lintegral_mono hbd
    _ = (C.toNNReal : ℝ≥0∞) * lam S := by rw [setLIntegral_const]

end GlobalTheory.CompanionTheory.WeilSiegel.Free.FibreBound
