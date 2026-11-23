import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Statements
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.SectionInjectivityHypothesesProjectiveLine
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.ChartPowNeZero
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (chartRingZ)

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

omit [Fintype ι] in

theorem genPt_ne_zero_of_isLive {P : ArithVariety n} {c : (k : ι) → Fin (n k + 1)}
    (hc : IsLive P c) (k : ι) : genPt P ⟨k, c k⟩ ≠ 0 := by
  intro h
  have h1 : Ideal.Quotient.mk P.ideal (X ⟨k, c k⟩) = 0 :=
    IsFractionRing.injective (CoordRing P) (FunField P) (h.trans (map_zero _).symm)
  exact hc k (Ideal.Quotient.eq_zero_iff_mem.mp h1)

theorem chartPow_ne_zero_of_isLive {P : ArithVariety n} {c : (k : ι) → Fin (n k + 1)}
    (hc : IsLive P c) (a : ι → ℤ) : chartPow P c a ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun k _ ↦ zpow_ne_zero _ (genPt_ne_zero_of_isLive hc k)

namespace AddBlockData

variable {P : ArithVariety n} (D : AddBlockData P)

theorem ξ_div_ξ_eq {c : (k : ι) → Fin (n k + 1)} (hc : IsLive P c) (i j : Fin (D.m + 1)) :
    D.ξ c i / D.ξ c j = D.x i / D.x j :=
  mul_div_mul_right _ _ (chartPow_ne_zero_of_isLive hc _)

theorem chartRingZ_chartPlus_eq {c : (k : ι) → Fin (n k + 1)} (hc : IsLive P c)
    (j : Fin (D.m + 1)) :
    chartRingZ D.yPlus (D.chartPlus c j) =
      Algebra.adjoin ℤ ((chartRing P c : Set (FunField P)) ∪
        Set.range fun i ↦ D.ξ c i / D.ξ c j) := by
  have hrange : (Set.range fun p : Coord D.dims ↦ D.yPlus p / D.yPlus ⟨p.1, D.chartPlus c j p.1⟩) =
      (Set.range fun v : Coord n ↦ genPt P v / genPt P ⟨v.1, c v.1⟩) ∪
        Set.range fun i ↦ D.ξ c i / D.ξ c j := by
    ext x
    constructor
    · rintro ⟨⟨_ | k, i⟩, rfl⟩
      · exact Or.inr ⟨i, D.ξ_div_ξ_eq hc i j⟩
      · exact Or.inl ⟨⟨k, i⟩, rfl⟩
    · rintro (⟨v, rfl⟩ | ⟨i, rfl⟩)
      · exact ⟨⟨some v.1, v.2⟩, rfl⟩
      · exact ⟨⟨none, i⟩, (D.ξ_div_ξ_eq hc i j).symm⟩
  rw [chartRingZ, hrange]
  apply le_antisymm
  · refine Algebra.adjoin_mono (Set.union_subset_union_left _ fun x hx ↦ ?_)
    exact Algebra.subset_adjoin hx
  · rw [Algebra.adjoin_le_iff]
    refine Set.union_subset (fun x hx ↦ ?_) fun x hx ↦ Algebra.subset_adjoin (Or.inr hx)
    exact Algebra.adjoin_mono Set.subset_union_left hx

theorem adjoin_ξ_div_eq_adjoin_inv {c : (k : ι) → Fin (n k + 1)} (hc : IsLive P c)
    (j : Fin (D.m + 1)) :
    Algebra.adjoin ℤ ((chartRing P c : Set (FunField P)) ∪ Set.range fun i ↦ D.ξ c i / D.ξ c j) =
      Algebra.adjoin ℤ ((chartRing P c : Set (FunField P)) ∪ {(D.ξ c j)⁻¹}) := by
  set S := Algebra.adjoin ℤ ((chartRing P c : Set (FunField P)) ∪ {(D.ξ c j)⁻¹})
  set T := Algebra.adjoin ℤ ((chartRing P c : Set (FunField P)) ∪
    Set.range fun i ↦ D.ξ c i / D.ξ c j)
  have hAS : (chartRing P c : Set (FunField P)) ⊆ S := fun x hx ↦ Algebra.subset_adjoin (Or.inl hx)
  have hAT : (chartRing P c : Set (FunField P)) ⊆ T := fun x hx ↦ Algebra.subset_adjoin (Or.inl hx)
  apply le_antisymm
  · rw [Algebra.adjoin_le_iff]
    rintro x (hx | ⟨i, rfl⟩)
    · exact hAS hx
    · show D.ξ c i / D.ξ c j ∈ S
      rw [div_eq_mul_inv]
      exact S.mul_mem (hAS (D.chart c hc i)) (Algebra.subset_adjoin (Or.inr rfl))
  · rw [Algebra.adjoin_le_iff]
    rintro x (hx | hx)
    · exact hAT hx
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      obtain ⟨u, hu, hsum⟩ := D.unit c hc
      have h : (D.ξ c j)⁻¹ = ∑ i, u i * (D.ξ c i / D.ξ c j) := by
        rw [← one_mul (D.ξ c j)⁻¹, ← hsum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        simp only [ξ]
        ring
      rw [h]
      exact T.sum_mem fun i _ ↦ T.mul_mem (hAT (hu i)) (Algebra.subset_adjoin (Or.inr ⟨i, rfl⟩))

end AddBlockData

theorem ChartRingDescription.chartRingDescription_alt_holds : ChartRingDescription.Statement := by
  intro ι _ _ n P D c hc j
  exact ⟨D.chartRingZ_chartPlus_eq hc j,
    (D.chartRingZ_chartPlus_eq hc j).trans (D.adjoin_ξ_div_eq_adjoin_inv hc j)⟩

theorem ChartRingDescription.equiv :
    GroundTheory.Heights₂.Heights.ChartRingDescription.Statement ↔
      GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close.ChartRingDescription.Statement :=
  iff_of_true GroundTheory.Heights₂.Heights.ChartRingDescription.proof ChartRingDescription.chartRingDescription_alt_holds

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
