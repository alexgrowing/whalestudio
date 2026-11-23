import Mathlib
import Formalism.PeriodIntegrals.VolSemiDirect
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.RestrProd
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.HformSmulRight
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.DensGen
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.FibDis
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TensAll

noncomputable section

namespace PI.DegenerateSiegelWeil.FibUniq

open MeasureTheory Topology Set Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped ENNReal

section Gen

variable {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V] [T2Space V]
  [LocallyCompactSpace V] [SecondCountableTopology V]
  [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [T2Space X]
  [LocallyCompactSpace X]
  {μ : Measure V} {ν : Measure X} [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν]
  [ν.IsOpenPosMeasure]
  {f : V → Y} {ι : X → Y} {U : Set V} {fib1 fib2 : X → Measure V}

theorem integral_eq (h1 : IsFibreFamily μ f ι U ν univ fib1)
    (h2 : IsFibreFamily μ f ι U ν univ fib2) {f' : V → X} (hf' : Continuous f')
    (hff' : ∀ v, f v = ι (f' v)) (hι : Function.Injective ι) (φ : V → ℝ) (hφc : Continuous φ)
    (hφs : HasCompactSupport φ) (hφU : tsupport φ ⊆ U) (b : X) :
    ∫ v, φ v ∂(fib1 b) = ∫ v, φ v ∂(fib2 b) := by
  have c1 := (h1.2.2 φ hφc hφs hφU).2
  have c2 := (h2.2.2 φ hφc hφs hφU).2
  have h0 : ∀ S, IsCompact S → S ⊆ univ →
      ∫ b in S, (∫ v, φ v ∂(fib1 b) - ∫ v, φ v ∂(fib2 b)) ∂ν = 0 := by
    intro S hS _
    rw [integral_sub ((c1.mono (subset_univ S)).integrableOn_compact hS)
      ((c2.mono (subset_univ S)).integrableOn_compact hS),
      ← PI.VolStabSW.DensGen.fib_set h1 hf' hff' hι φ hφc hφs hφU S hS (subset_univ S),
      ← PI.VolStabSW.DensGen.fib_set h2 hf' hff' hι φ hφc hφs hφU S hS (subset_univ S), sub_self]
  exact sub_eq_zero.1 (PI.VolStabSW.DensGen.eq_zero_of_setIntegral (ν := ν)
    (fun b => ∫ v, φ v ∂(fib1 b) - ∫ v, φ v ∂(fib2 b)) univ b univ_mem (c1.sub c2) h0)

theorem fin_cpt {fib : X → Measure V} (h : IsFibreFamily μ f ι U ν univ fib) (hU : IsOpen U)
    (b : X) (K : Set V) (hK : IsCompact K) (hKU : K ⊆ U) : fib b K < ⊤ := by
  obtain ⟨g, hgK, hgc, hgU, -⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen hK hU hKU
  have hi := (h.2.2 g g.continuous hgc hgU).1 b (mem_univ b)
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  calc fib b K = ∫⁻ v, K.indicator 1 v ∂fib b := (lintegral_indicator_one hKm).symm
    _ ≤ ∫⁻ v, ENNReal.ofReal (g v) ∂fib b := lintegral_mono fun v => by
        by_cases hv : v ∈ K
        · simp [hv, hgK hv]
        · simp [hv]
    _ < ⊤ := hi.lintegral_lt_top

theorem open_eq (h1 : IsFibreFamily μ f ι U ν univ fib1)
    (h2 : IsFibreFamily μ f ι U ν univ fib2) {f' : V → X} (hf' : Continuous f')
    (hff' : ∀ v, f v = ι (f' v)) (hι : Function.Injective ι) (O : Set V) (hO : IsOpen O)
    (hOU : O ⊆ U) (b : X) : fib1 b O = fib2 b O := by
  obtain ⟨φ, hφ, h01, hmono, hlim⟩ := PI.VolStabSW.DiscreteGroups.approx O hO
  have hmeas : ∀ k, Measurable fun v => ENNReal.ofReal (φ k v) :=
    fun k => ENNReal.measurable_ofReal.comp (hφ k).1.measurable
  have hmon : Monotone fun k v => ENNReal.ofReal (φ k v) :=
    fun i j hij v => ENNReal.ofReal_le_ofReal (hmono v hij)
  have key : ∀ fib : X → Measure V, IsFibreFamily μ f ι U ν univ fib →
      fib b O = ⨆ k, ENNReal.ofReal (∫ v, φ k v ∂(fib b)) := by
    intro fib hf
    calc fib b O = ∫⁻ v, O.indicator 1 v ∂(fib b) :=
          (lintegral_indicator_one hO.measurableSet).symm
      _ = ∫⁻ v, ⨆ k, ENNReal.ofReal (φ k v) ∂(fib b) := lintegral_congr fun v => (hlim v).symm
      _ = ⨆ k, ∫⁻ v, ENNReal.ofReal (φ k v) ∂(fib b) := lintegral_iSup hmeas hmon
      _ = ⨆ k, ENNReal.ofReal (∫ v, φ k v ∂(fib b)) := by
          congr 1
          funext k
          exact (ofReal_integral_eq_lintegral_ofReal
            ((hf.2.2 _ (hφ k).1 (hφ k).2.1 ((hφ k).2.2.trans hOU)).1 b (mem_univ b))
            (ae_of_all _ fun v => (h01 k v).1)).symm
  rw [key fib1 h1, key fib2 h2]
  congr 1
  funext k
  rw [integral_eq h1 h2 hf' hff' hι (φ k) (hφ k).1 (hφ k).2.1 ((hφ k).2.2.trans hOU) b]

theorem fib_eq (h1 : IsFibreFamily μ f ι U ν univ fib1)
    (h2 : IsFibreFamily μ f ι U ν univ fib2) {f' : V → X} (hf' : Continuous f')
    (hff' : ∀ v, f v = ι (f' v)) (hι : Function.Injective ι) (hU : IsOpen U) : fib1 = fib2 := by
  funext b
  obtain ⟨W, hW, hWU⟩ := PI.VolStabSW.DiscreteGroups.cover U hU
  have hWsub : ∀ n, W n ⊆ U := fun n => subset_closure.trans (hW n).2.2
  have hnull : ∀ fib : X → Measure V, IsFibreFamily μ f ι U ν univ fib → fib b Uᶜ = 0 :=
    fun fib hf => measure_mono_null (compl_subset_compl.2 inter_subset_right) (hf.1 b)
  have hfin : ∀ fib : X → Measure V, IsFibreFamily μ f ι U ν univ fib → ∀ n, fib b (W n) ≠ ⊤ :=
    fun fib hf n => (lt_of_le_of_lt (measure_mono subset_closure)
      (fin_cpt hf hU b _ (hW n).2.1 (hW n).2.2)).ne
  let s : Option ℕ → Set V := fun o => o.elim Uᶜ W
  have hs : ⋃ o, s o = univ := by
    rw [iUnion_option]
    simp only [s, Option.elim_none, Option.elim_some]
    rw [hWU, compl_union_self]
  refine (Measure.ext_iff_of_iUnion_eq_univ hs).2 fun o => ?_
  cases o with
  | none =>
    simp only [s, Option.elim_none]
    rw [Measure.restrict_eq_zero.2 (hnull fib1 h1), Measure.restrict_eq_zero.2 (hnull fib2 h2)]
  | some n =>
    simp only [s, Option.elim_some]
    have : IsFiniteMeasure ((fib1 b).restrict (W n)) :=
      isFiniteMeasure_restrict.2 (hfin fib1 h1 n)
    refine ext_of_generate_finite {t : Set V | IsOpen t} (BorelSpace.measurable_eq.trans rfl)
      isPiSystem_isOpen (fun t ht => ?_) ?_
    · rw [Measure.restrict_apply ht.measurableSet, Measure.restrict_apply ht.measurableSet]
      exact open_eq h1 h2 hf' hff' hι _ (ht.inter (hW n).1) (inter_subset_right.trans (hWsub n)) b
    · rw [Measure.restrict_apply_univ, Measure.restrict_apply_univ]
      exact open_eq h1 h2 hf' hff' hι _ (hW n).1 (hWsub n) b

end Gen

section Tens

open scoped TensorProduct
open PI.VolStabSW PI.VolStabSW.TensAllW

end Tens

end PI.DegenerateSiegelWeil.FibUniq

namespace PI.DegenerateSiegelWeil

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain MeasureTheory PI.VolStabSW
  PI.VolStabSW.TensAllW

end PI.DegenerateSiegelWeil
