import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanNecTemp
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.PropsCos
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology
open MeasureTheory ValuativeRel

noncomputable section
namespace GlobalTheory.CompanionTheory.NabsContract

theorem valuation_lt_one_of_tendsto_pow {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (t : kˣ)
    (ht : Tendsto (fun n : ℕ => (t : k) ^ n) atTop (𝓝 0)) : valuation k (t : k) < 1 := by
  by_contra H
  rw [not_lt] at H
  have hs : {x : k | valuation k x < 1} ∈ 𝓝 (0 : k) :=
    (IsValuativeTopology.mem_nhds_zero_iff _).mpr ⟨1, fun x hx => by simpa using hx⟩
  obtain ⟨n, hn⟩ := (ht.eventually hs).exists
  have hn' : valuation k ((t : k) ^ n) < 1 := hn
  rw [map_pow] at hn'
  exact (not_lt.mpr (one_le_pow₀ H)) hn'

theorem nabs_lt_one_of_tendsto_pow : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (t : kˣ),
    Tendsto (fun n : ℕ => (t : k) ^ n) atTop (𝓝 0) → nabs k t < 1 := by
  intro k _ _ _ _ t ht
  have hv := GlobalTheory.CompanionTheory.NabsContract.valuation_lt_one_of_tendsto_pow t ht
  letI : MeasurableSpace k := borel k
  haveI : BorelSpace k := ⟨rfl⟩
  haveI := GlobalTheory.SplitWeil.t2Space k
  set ν : Measure k := Measure.addHaar with hν
  set O : Set k := ((valuation k).integer : Set k) with hO_def
  set B : Set k := GlobalTheory.SplitWeil.cball t with hB_def
  have hO : IsOpen O := GlobalTheory.SplitWeil.isOpen_int k
  have hBO : B ⊆ O := fun x hx =>
    (Valuation.mem_integer_iff _ _).mpr
      (le_trans (show valuation k x ≤ valuation k (t : k) from hx) hv.le)
  have hO1 : O ⊆ GlobalTheory.SplitWeil.cball (1 : kˣ) := fun x hx => by
    have hx' := (Valuation.mem_integer_iff _ _).mp hx
    show valuation k x ≤ valuation k ((1 : kˣ) : k)
    rw [Units.val_one, map_one]
    exact hx'
  have hOfin : ν O ≠ ⊤ :=
    measure_ne_top_of_subset hO1 (GlobalTheory.SplitWeil.isCompact_cball (1 : kˣ)).measure_lt_top.ne
  have hBfin : ν B ≠ ⊤ := measure_ne_top_of_subset hBO hOfin
  have h1 : (1 : k) ∈ O \ B := by
    refine ⟨(Valuation.mem_integer_iff _ _).mpr (map_one _).le, fun h => ?_⟩
    have h' : valuation k (1 : k) ≤ valuation k (t : k) := h
    rw [map_one] at h'
    exact not_lt.mpr h' hv
  have hdiff : 0 < ν (O \ B) :=
    (hO.sdiff (GlobalTheory.SplitWeil.isCompact_cball t).isClosed).measure_pos ν ⟨1, h1⟩
  rw [measure_sdiff hBO (GlobalTheory.SplitWeil.isOpen_cball t).measurableSet.nullMeasurableSet
    hBfin, tsub_pos_iff_lt] at hdiff
  have hlt : ν.real B < ν.real O := (ENNReal.toReal_lt_toReal hBfin hOfin).mpr hdiff
  have hOpos : 0 < ν.real O :=
    ENNReal.toReal_pos (hO.measure_pos ν ⟨0, (Valuation.mem_integer_iff _ _).mpr (by simp)⟩).ne'
      hOfin
  have hmeas : ν.real B = GlobalTheory.SplitWeil.nabs k t * ν.real O :=
    GlobalTheory.SplitWeil.measureReal_cball ν t
  rw [hmeas] at hlt
  exact lt_of_mul_lt_mul_right (by rwa [one_mul]) hOpos.le

end GlobalTheory.CompanionTheory.NabsContract
