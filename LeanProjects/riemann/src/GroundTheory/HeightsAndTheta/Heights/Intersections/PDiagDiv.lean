import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsDiagDiv
import GroundTheory.HeightsAndTheta.Heights.Intersections.PRFormula
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDivCycleMul
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI

noncomputable section

namespace DiagonalDivisor

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem divCycle_of_mem {P W : Ideal (MRing ι)} {s : MRing ι} (hW : W ∈ divSupp P s) :
    divCycle P s W = multAt (P ⊔ Ideal.span {s}) W := by
  unfold divCycle
  simp [Finsupp.ofSupportFinite_coe, hW]

theorem divCycle_of_not_mem {P W : Ideal (MRing ι)} {s : MRing ι} (hW : W ∉ divSupp P s) :
    divCycle P s W = 0 := by
  unfold divCycle
  simp [Finsupp.ofSupportFinite_coe, hW]

open Classical in

theorem divCycle_eq_ite {P : Ideal (MRing ι)} [P.IsPrime] {s u : MRing ι} (hu : u ∉ P)
    (W : Ideal (MRing ι)) :
    divCycle P s W = if W ∈ divSupp P (s * u) then multAt (P ⊔ Ideal.span {s}) W else 0 := by
  by_cases hW : W ∈ divSupp P (s * u)
  · rw [if_pos hW]
    by_cases hWs : W ∈ divSupp P s
    · exact divCycle_of_mem hWs
    rw [divCycle_of_not_mem hWs]
    have hWp : W.IsPrime := hW.1.1.1
    by_cases hsW : s ∈ W
    · exfalso
      refine hWs ⟨⟨⟨hWp, sup_le (le_sup_left.trans hW.1.1.2)
        ((Ideal.span_singleton_le_iff_mem _).mpr hsW)⟩, fun Q hQ hQW => hW.1.2 ⟨hQ.1, ?_⟩ hQW⟩, hW.2⟩
      exact (sup_le_sup_left ((Ideal.span_singleton_le_iff_mem _).mpr
        (Ideal.mul_mem_right u _ (Ideal.mem_span_singleton_self s))) P).trans hQ.2
    · have hnle : ¬ P ⊔ Ideal.span {s} ≤ W := fun h => hsW (h (Ideal.mem_sup_right (Ideal.subset_span rfl)))
      unfold multAt
      rw [dif_pos hWp, Module.length_eq_zero_iff.mpr
        (NumbersDVR.localizedQuot_subsingleton_of_not_le _ W hnle)]
      rfl
  · rw [if_neg hW]
    refine divCycle_of_not_mem fun hWs => hW ⟨?_, hWs.2⟩
    exact NumbersDVR.mem_minimalPrimes_sup_span_mul hu hWs.1

end DiagonalDivisor

open DiagonalDivisor in

theorem DiagDiv.proof (hF : DiagForms.Statement) (hO : DiagOrd.Statement) : DiagDiv.Statement := by
  intro Ω _ ι ν κ _ _ _ E _ _ Φ _ _ x B e φ δ hS hG hD hx a ha
  refine ⟨hF Ω ι ν κ E Φ x B e φ δ hS hG hD hx a ha, ?_⟩
  intro n g h hg hh hP hq
  obtain ⟨hΔ, hW⟩ := hO Ω ι ν κ E Φ x B e φ δ hS hG hD hx a ha n g h hg hh hP hq
  have hPp : (T.wwIdeal x δ e φ (a 0) (a 1)).IsPrime := RingHom.ker_isPrime _
  have ht : T.diagSec a ≠ 0 := by
    unfold T.diagSec
    exact sub_ne_zero.mpr (fun h01 => absurd (ha.injective h01) (by decide))
  have hgP : g ∉ T.wwIdeal x δ e φ (a 0) (a 1) := by
    have hh' := (DiagRAux.not_mem_ker_iff_aeval_ne _ h _ hh).1 hP
    exact (DiagRAux.not_mem_ker_iff_aeval_ne _ g _ hg).2 (hq ▸ mul_ne_zero ht hh')
  ext W
  have hcg := divCycle_eq_ite (s := g) hP W
  have hch := divCycle_eq_ite (s := h) hgP W
  rw [mul_comm h g] at hch
  simp only [T.toZCycle, Finsupp.coe_sub, Pi.sub_apply, Finsupp.mapRange_apply, Finsupp.single_apply, hcg, hch]
  by_cases hWm : W ∈ divSupp (T.wwIdeal x δ e φ (a 0) (a 1)) (g * h)
  · rw [if_pos hWm, if_pos hWm, hW W hWm]
    simp only [eq_comm]
  · rw [if_neg hWm, if_neg hWm, if_neg (fun h' : T.wwIdeal x δ e φ (a 0) (a 0) = W => hWm (h' ▸ hΔ))]
    simp

end

end GroundTheory.Heights₂.Heights.Inter
