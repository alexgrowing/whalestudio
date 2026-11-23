import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnalyticLogResolution
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PointDimensionLtProjectiveLine
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LogResolutionProjectiveLine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableSetInterPreimage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOnNhdOffBoundary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundaryPotentialSectionBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankDropOfAnalyticSetDimension

namespace GlobalTheory.LogResInt
open MeasureTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions
open scoped ENNReal

theorem logNormIntegrablePoincare (hR : GlobalTheory.Published.AnalyticLogResolution)
    (hD : GlobalTheory.Published.AnalyticSetDimension) : LogNormIntegrablePoincare := by
  intro d X _ _ _ A hproj m α Λ σ c hset Z n hZ hreg hZbd L s hL hs hs1 hsZ hcomp
  have ht : ∀ i, IsPotential A ((Fin.cons L Λ : Fin (m + 1) → LocPot X) i) ∧
      IsSection A ((Fin.cons L Λ : Fin (m + 1) → LocPot X) i) ((Fin.cons s σ : Fin (m + 1) → X → X → ℂ) i) ∧
      ∃ y ∈ Z, (Fin.cons s σ : Fin (m + 1) → X → X → ℂ) i y y ≠ 0 := by
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · exact ⟨hL, hs, hsZ⟩
    · obtain ⟨y, hyZ, hybd⟩ := Set.not_subset.1 hZbd
      exact ⟨(hset.2.2.1 i).1, (hset.2.2.1 i).2.1, y, hyZ, fun h => hybd ⟨i, h⟩⟩
  obtain ⟨Y, tY, cY, t2Y, B, μ, hμ, S, r, W, e, J, hBproj, hrange, hS, -, hdense, hinj, himm, hSW, hsnc⟩ :=
    hR d X A hproj Z n hZ hreg (m + 1) _ _ ht
  have hhyp : ∀ y, ∃ χ : OpenPartialHomeomorph Y (Fin n → ℂ), IsCompatChart B χ ∧ y ∈ χ.source ∧
      ∃ J' : Finset (Fin n), μ ⁻¹' S ∩ χ.source = {w ∈ χ.source | ∃ a ∈ J', χ w a = 0} := by
    intro y
    obtain ⟨χ, hχ, hy, κ, -, hW, -⟩ := hsnc y
    classical
    refine ⟨χ, hχ, hy, Finset.univ.filter (fun a => ∃ k ∈ J, κ k = some a), ?_⟩
    ext w
    simp only [hSW, Set.mem_inter_iff, Set.mem_iUnion, Set.mem_setOf_eq, Finset.mem_filter,
      Finset.mem_univ, true_and, exists_prop]
    constructor
    · rintro ⟨⟨k, hk, hwk⟩, hw⟩
      have := (hW k).le ⟨hwk, hw⟩
      obtain ⟨a, ha, hwa⟩ := this.2
      exact ⟨hw, a, ⟨k, hk, ha⟩, hwa⟩
    · rintro ⟨hw, a, ⟨k, hk, ha⟩, hwa⟩
      have : w ∈ W k ∩ χ.source := (hW k).ge ⟨hw, a, ha, hwa⟩
      exact ⟨⟨k, hk, this.1⟩, hw⟩
  have h1 := GlobalTheory.RegToResolution.regIntegral_le_chartSumInt d X A Z n Y B μ hμ S (boundary σ) hrange hS hdense hinj himm hhyp
    (poincarePot α Λ σ c)
    (GlobalTheory.PoincSmooth.smoothOn_nhd_off_boundary d X A m α Λ σ c hset.1 (fun i => ⟨(hset.2.2.1 i).1, (hset.2.2.1 i).2.1⟩)
      (fun i => (hset.2.2.1 i).2.2.2)) (absLogNorm L s)
  have h2 := GlobalTheory.T.boundary_potential_section_bound d X A m α Λ σ c hset L s hL hs hs1 n Y B hBproj μ hμ r W e hsnc
    (GlobalTheory.LogResInt.rankDrop_of_analyticSetDimension hD d X A m Λ σ (fun i => ⟨(hset.2.2.1 i).1, (hset.2.2.1 i).2.1⟩) Z n hZ hreg hZbd L s hL hs hsZ
      hcomp Y B μ hμ hrange r W e hsnc)
  exact lt_of_le_of_lt h1 h2

end GlobalTheory.LogResInt
