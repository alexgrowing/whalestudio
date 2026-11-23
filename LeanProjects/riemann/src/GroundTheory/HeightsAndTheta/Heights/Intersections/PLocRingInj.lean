import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StLocRingInj
import GroundTheory.HeightsAndTheta.Heights.Intersections.PLocRingLocal
import GroundTheory.HeightsAndTheta.Heights.Intersections.PLocRingFrac
import GroundTheory.HeightsAndTheta.Heights.Intersections.LogCardLocIdealUnitMul
import GroundTheory.HeightsAndTheta.Heights.Intersections.AvoidRing
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem LocRingInj.le_of_locRing_eq {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P W W' : Ideal (MRing ι)} (hP : P.IsPrime) (hW : IsMultiProjPrime W) (hW' : IsMultiProjPrime W')
    (hPW : P ≤ W) (hPW' : P ≤ W') (heq : locRing P W = locRing P W') : W ≤ W' := by
  classical
  have := hP
  have hL := LocRingLocal.proof LocRingFrac.proof
  set φ := algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) with hφ
  have hne : ∀ {f : MRing ι}, f ∉ P → φ (Ideal.Quotient.mk P f) ≠ 0 := fun hf h => hf <| by
    rwa [hφ, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem] at h

  have hunit : ∀ {y : FractionRing (MRing ι ⧸ P)} (hy : y ∈ locRing P W) (hy' : y ∈ locRing P W'),
      IsUnit (⟨y, hy'⟩ : locRing P W') → IsUnit (⟨y, hy⟩ : locRing P W) := by
    intro y hy hy' hu
    obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.mp hu
    have hb' : y * (b : FractionRing (MRing ι ⧸ P)) = 1 := by
      have := congrArg Subtype.val hb
      rwa [Subring.coe_mul, Subring.coe_one, Subtype.coe_mk] at this
    have hbW : (b : FractionRing (MRing ι ⧸ P)) ∈ locRing P W := by rw [heq]; exact b.2
    refine IsUnit.of_mul_eq_one (⟨b, hbW⟩ : locRing P W) (Subtype.ext ?_)
    rw [Subring.coe_mul, Subring.coe_one, Subtype.coe_mk, Subtype.coe_mk, hb']
  choose i hi using hW.2.2
  choose j hj using hW'.2.2

  have hjW : ∀ k, (X ⟨k, j k⟩ : MRing ι) ∉ W := by
    intro k
    have hiP : (X ⟨k, i k⟩ : MRing ι) ∉ P := fun h => hi k (hPW h)
    have hjP : (X ⟨k, j k⟩ : MRing ι) ∉ P := fun h => hj k (hPW' h)
    have h1 : φ (Ideal.Quotient.mk P (X ⟨k, i k⟩)) / φ (Ideal.Quotient.mk P (X ⟨k, j k⟩)) ∈ locRing P W :=
      heq ▸ frac_mem_locRing hPW' (AvoidRing.isMultiHomog_X k (i k)) (AvoidRing.isMultiHomog_X k (j k))
        (hj k) (div_mul_cancel₀ _ (hne hjP))
    have h2 : φ (Ideal.Quotient.mk P (X ⟨k, j k⟩)) / φ (Ideal.Quotient.mk P (X ⟨k, i k⟩)) ∈ locRing P W :=
      frac_mem_locRing hPW (AvoidRing.isMultiHomog_X k (j k)) (AvoidRing.isMultiHomog_X k (i k))
        (hi k) (div_mul_cancel₀ _ (hne hiP))
    have hu : IsUnit (⟨_, h2⟩ : locRing P W) := by
      refine IsUnit.of_mul_eq_one (⟨_, h1⟩ : locRing P W) (Subtype.ext ?_)
      rw [Subring.coe_mul, Subring.coe_one, Subtype.coe_mk, Subtype.coe_mk]
      have := hne hiP
      have := hne hjP
      field_simp
    exact ((hL K ι P W hP hW.1 hPW).2 _ _ _ _ (AvoidRing.isMultiHomog_X k (j k))
      (AvoidRing.isMultiHomog_X k (i k)) (hi k) (div_mul_cancel₀ _ (hne hiP))).mp hu

  obtain ⟨S, hS, hWS⟩ := hW.2.1
  rw [hWS, Ideal.span_le]
  intro f hf
  obtain ⟨a, ha⟩ := hS f hf
  have hfW : f ∈ W := hWS ▸ Ideal.subset_span hf
  by_contra hfW'
  have htW := AvoidRing.coordProd_not_mem hW.1 j hjW a
  have htW' := AvoidRing.coordProd_not_mem hW'.1 j hj a
  have ht := AvoidRing.isMultiHomog_coordProd (R := ℤ) (ι := ι) j a
  have hy := div_mul_cancel₀ (φ (Ideal.Quotient.mk P f)) (hne fun h => htW (hPW h))
  have hyW := frac_mem_locRing hPW ha ht htW hy
  have hyW' := frac_mem_locRing hPW' ha ht htW' hy
  have hu' : IsUnit (⟨_, hyW'⟩ : locRing P W') :=
    ((hL K ι P W' hP hW'.1 hPW').2 _ f _ a ha ht htW' hy).mpr hfW'
  exact ((hL K ι P W hP hW.1 hPW).2 _ f _ a ha ht htW hy).mp (hunit hyW hyW' hu') hfW

theorem LocRingInj.proof : LocRingInj.Statement := by
  intro K _ ι _ P W W' hP hW hW' hPW hPW' heq
  exact le_antisymm (LocRingInj.le_of_locRing_eq hP hW hW' hPW hPW' heq)
    (LocRingInj.le_of_locRing_eq hP hW' hW hPW' hPW heq.symm)

end

end GroundTheory.Heights₂.Heights.Inter
