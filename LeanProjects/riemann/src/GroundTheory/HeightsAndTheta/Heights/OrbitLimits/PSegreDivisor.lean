import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.MemMinimalPrimesOfMemDivSuppDivSupp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.SwapLoc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.InhDivCycleOfSuppEmpty
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsMonomialNotMem
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsSegreDivisor
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsSegreComponent
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

universe u v w

theorem multAt_pos_of_mem_divSupp_field {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
    {F : Type*} [Field F] {V W : Ideal (MRingOver F ι)} {f : MRingOver F ι}
    (hW : W ∈ divSupp V f) : 0 < multAt (V ⊔ Ideal.span {f}) W := by
  have hmin := hW.1
  have hWp : W.IsPrime := hmin.1.1
  have hm : IsLocalRing.maximalIdeal (Localization.AtPrime W) ∈
      ((V ⊔ Ideal.span {f}).map (algebraMap (MRingOver F ι) (Localization.AtPrime W))).minimalPrimes := by
    rw [IsLocalization.minimalPrimes_map W.primeCompl (Localization.AtPrime W)]
    rw [Set.mem_preimage, Localization.AtPrime.under_maximalIdeal]
    exact hmin
  have hne := SwapLoc.length_quot_ne_top_of_mem_minimalPrimes _ hm
  have : Nontrivial (Localization.AtPrime W ⧸
      (V ⊔ Ideal.span {f}).map (algebraMap (MRingOver F ι) (Localization.AtPrime W))) :=
    Ideal.Quotient.nontrivial_iff.mpr
      (ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal _).ne_top hm.1.2)
  have hpos := Module.length_pos (R := Localization.AtPrime W)
    (M := Localization.AtPrime W ⧸
      (V ⊔ Ideal.span {f}).map (algebraMap (MRingOver F ι) (Localization.AtPrime W)))
  rw [multAt, dif_pos hWp, inh_length_locQuot]
  exact ENat.toNat_pos hpos.ne' hne

theorem SegreDivisor.proof (h₁ : SegreComponent.Statement.{u, v, w}) :
    SegreDivisor.Statement.{u, v, w} := by
  intro K _ ι _ F _ V n hV
  obtain ⟨i, hi⟩ : ∃ i : ∀ k, ι k, IsChart V i :=
    ⟨fun k => (hV.1.2.2 k).choose, fun k => (hV.1.2.2 k).choose_spec⟩
  refine ⟨_, isMultiHomog_coordProd (F := F) i (fun _ => 1), coordProd_not_mem hV.1.1 i hi _, ?_⟩
  obtain ⟨W, hW⟩ := h₁ K ι F V n _ hV (isMultiHomog_coordProd (F := F) i (fun _ => 1))
  intro h0
  have hpos := multAt_pos_of_mem_divSupp_field hW
  rw [← DivisorCycleSwap.divCycle_apply_of_mem hW, h0, Finsupp.zero_apply] at hpos
  exact lt_irrefl _ hpos

end GroundTheory.Heights₂.Heights.Targets
