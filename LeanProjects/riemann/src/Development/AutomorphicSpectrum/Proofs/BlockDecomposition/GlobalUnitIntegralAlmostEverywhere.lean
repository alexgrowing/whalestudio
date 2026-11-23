import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsReps

open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver
open GlobalTheory.CompanionTheory.FexTheta

noncomputable section

namespace GlobalTheory.CompanionTheory.KUnit

theorem finite_nonunit_places (K : Type) [Field K] [NumberField K] (κ : Kˣ) :
    {w : PlK K | 1 < w.valuation K (κ : K) ∨ 1 < w.valuation K ((κ⁻¹ : Kˣ) : K)}.Finite := by
  have h1 := HeightOneSpectrum.Support.finite (𝓞 K) (κ : K)
  have h2 := HeightOneSpectrum.Support.finite (𝓞 K) ((κ⁻¹ : Kˣ) : K)
  exact (h1.union h2).subset fun w hw => hw

theorem subsingleton_below (K : Type) [Field K] [NumberField K] (w : PlK K) :
    {v : Pl | w.asIdeal.LiesOver v.asIdeal}.Subsingleton := by
  intro v hv v' hv'
  have h1 : v.asIdeal = w.asIdeal.under (𝓞 ℚ) := (hv : w.asIdeal.LiesOver v.asIdeal).over
  have h2 : v'.asIdeal = w.asIdeal.under (𝓞 ℚ) := (hv' : w.asIdeal.LiesOver v'.asIdeal).over
  exact HeightOneSpectrum.ext (h1.trans h2.symm)

theorem mem_integer_of_val (K : Type) [Field K] [NumberField K] (w : PlK K) {k : K}
    (h : ¬ 1 < w.valuation K k) : algebraMap K (Kv K w) k ∈ 𝒪[Kv K w] := by
  have hmem : algebraMap K (Kv K w) k ∈ w.adicCompletionIntegers K := by
    have e : Valued.v (algebraMap K (w.adicCompletion K) k) = w.valuation K k :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w k
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    exact e.le.trans (not_lt.1 h)
  exact (mem_valuationInteger_iff w _).2 hmem

theorem unit_almost_everywhere : ∀ (K : Type) [Field K] [NumberField K] (κ : Kˣ), ∃ S : Finset Pl, ∀ v ∉ S, ∀ w : PlK K, w.asIdeal.LiesOver v.asIdeal →
  ((atW w κ : (Kv K w)ˣ) : Kv K w) ∈ 𝒪[Kv K w] ∧ (((atW w κ)⁻¹ : (Kv K w)ˣ) : Kv K w) ∈ 𝒪[Kv K w] := by
  intro K _ _ κ
  have hfin : {v : Pl | ∃ w ∈ {w : PlK K | 1 < w.valuation K (κ : K) ∨
      1 < w.valuation K ((κ⁻¹ : Kˣ) : K)}, w.asIdeal.LiesOver v.asIdeal}.Finite := by
    have := (finite_nonunit_places K κ).biUnion
      (t := fun w => {v : Pl | w.asIdeal.LiesOver v.asIdeal})
      (fun w _ => (subsingleton_below K w).finite)
    refine this.subset ?_
    rintro v ⟨w, hw, hv⟩
    exact Set.mem_biUnion hw hv
  refine ⟨hfin.toFinset, fun v hv w hw => ?_⟩
  have hnot : ¬ (1 < w.valuation K (κ : K) ∨ 1 < w.valuation K ((κ⁻¹ : Kˣ) : K)) := by
    intro h
    exact hv (hfin.mem_toFinset.2 ⟨w, h, hw⟩)
  rw [not_or] at hnot
  constructor
  · exact mem_integer_of_val K w hnot.1
  · have : (((atW w κ)⁻¹ : (Kv K w)ˣ) : Kv K w) = algebraMap K (Kv K w) ((κ⁻¹ : Kˣ) : K) := by
      simp [atW]
    rw [this]
    exact mem_integer_of_val K w hnot.2

end GlobalTheory.CompanionTheory.KUnit
