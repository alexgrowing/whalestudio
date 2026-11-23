import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpOverLocMaxCentreCut
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpValuationCentre
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

theorem BlowUpOverLocCentreDom.proof : BlowUpOverLocCentreDom.Statement.{u} := by
  intro O _ _ _ K _ _ ι _ J _ P n hP N u hu hu' c x hx hxP W hWmin hWrel
  have := hP.multiProj.isPrime
  intro 𝔫 h𝔫
  have hW : W.IsPrime := hWmin.1.1
  have hPW : P ≤ W := le_sup_left.trans hWmin.1.2
  obtain ⟨V, hBV, hnV⟩ := Ideal.image_subset_nonunits_valuationSubring 𝔫 h𝔫.ne_top
  obtain ⟨W', hp, hh, hr, hb, hc, hloc⟩ := exists_blowUp_centre (J := J) P W hP.multiProj.multiHomog hW hPW
    hWrel N u hu hu' V ((homLocRing_le_blowUpOverLoc P W u).trans hBV)
  have h : blowUpOverLoc P W u ≤ blowUpLocRing P u W' := iInf₂_le W' ⟨hp, hh, hr, hb, hc⟩
  refine ⟨W', hp, hh, hr, hb, hc, h, fun y hy hunit => ?_⟩
  obtain ⟨w, hw⟩ := hunit
  obtain ⟨hyV, hymax⟩ := (ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal (A := V)).1
    (hnV ⟨y, hy, rfl⟩)
  have hinv : ((w⁻¹ : (blowUpLocRing P u W')ˣ) : FractionRing (MRing ι O ⧸ P)) ∈ V := hloc ((w⁻¹ : (blowUpLocRing P u W')ˣ) : blowUpLocRing P u W').2
  have hmul : (y : FractionRing (MRing ι O ⧸ P)) * ((w⁻¹ : (blowUpLocRing P u W')ˣ) : _) = 1 := by
    have h1 := congrArg Subtype.val w.mul_inv
    rw [hw] at h1
    exact h1
  exact (IsLocalRing.mem_maximalIdeal _).1 hymax (IsUnit.of_mul_eq_one ⟨_, hinv⟩ (Subtype.ext hmul))

end

end GroundTheory.Heights₂.Heights.NumbersDVR
