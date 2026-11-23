import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaPartD
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundUnitary
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermInf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermOf
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteAdeleTopologyStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RatTuple
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SchwartzBruhatEqSumPure
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AdelicCharacterArchimedeanFormStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.StandardAdelicCharacterStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdeleHaarMapEqScaledVolumeStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField
open GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl GlobalTheory.CompanionTheory.SW.Core

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.CosetBound

theorem twisted_integral_finite_coset_combination_bound :
    ∀ (X : Type) [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    [SecondCountableTopology X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (m : Measure X) [m.IsAddHaarMeasure]
    (L : AddSubgroup X), IsCompact (L : Set X) → IsOpen (L : Set X) →
    ∀ (q : X → ℂ), Continuous q → (∀ x, ‖q x‖ = 1) → ∀ K : ℝ,
    (∀ x₀ : X, ‖∫ x in {y | y - x₀ ∈ L}, q x ∂m‖ ^ 2 ≤ K) →
    ∀ (Q : X → ℂ) (s : Finset X),
    (∀ x, Q x = ∑ a ∈ s, Q a * Set.indicator {y | y - a ∈ L} (fun _ => (1 : ℂ)) x) →
    ‖∫ x, Q x * q x ∂m‖ ≤ (∑ a ∈ s, ‖Q a‖) * √K := by
  intro X _ _ _ _ _ _ _ m _ L hc ho q hq hn K hK Q s hQ
  have hopen : ∀ a : X, IsOpen {y : X | y - a ∈ L} := fun a =>
    ho.preimage (continuous_id.sub continuous_const)
  have hmeas : ∀ a : X, MeasurableSet {y : X | y - a ∈ L} := fun a => (hopen a).measurableSet
  have hcomp : ∀ a : X, IsCompact {y : X | y - a ∈ L} := by
    intro a
    have himg : {y : X | y - a ∈ L} = (fun x => x + a) '' (L : Set X) := by
      ext y
      constructor
      · intro hy
        exact ⟨y - a, hy, by simp⟩
      · rintro ⟨x, hx, rfl⟩
        simpa using hx
    rw [himg]
    exact hc.image (continuous_id.add continuous_const)
  have hion : ∀ a : X, IntegrableOn q {y : X | y - a ∈ L} m := fun a =>
    hq.continuousOn.integrableOn_compact (hcomp a)
  have hterm : ∀ a : X, (fun x => Set.indicator {y : X | y - a ∈ L} (fun _ => (1 : ℂ)) x * q x)
      = Set.indicator {y : X | y - a ∈ L} q := by
    intro a
    funext x
    by_cases hx : x ∈ {y : X | y - a ∈ L}
    · simp only [Set.indicator_of_mem hx, one_mul]
    · simp only [Set.indicator_of_notMem hx, zero_mul]
  have hint : ∀ a : X, Integrable (Set.indicator {y : X | y - a ∈ L} q) m := fun a =>
    (integrable_indicator_iff (hmeas a)).2 (hion a)
  have hfun : (fun x => Q x * q x)
      = fun x => ∑ a ∈ s, Q a * Set.indicator {y : X | y - a ∈ L} q x := by
    funext x
    conv_lhs => rw [hQ x]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [mul_assoc, congrFun (hterm a) x]
  have hsum : ∫ x, Q x * q x ∂m = ∑ a ∈ s, Q a * ∫ x in {y : X | y - a ∈ L}, q x ∂m := by
    rw [hfun, integral_finsetSum s (fun a _ => (hint a).const_mul (Q a))]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [integral_const_mul, integral_indicator (hmeas a)]
  have hone : ∀ a : X, ‖∫ x in {y : X | y - a ∈ L}, q x ∂m‖ ≤ √K := by
    intro a
    have h := Real.abs_le_sqrt (hK a)
    rwa [abs_of_nonneg (norm_nonneg _)] at h
  rw [hsum, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hone a) (norm_nonneg _)

end GlobalTheory.CompanionTheory.SiegelND.Integ.CosetBound
