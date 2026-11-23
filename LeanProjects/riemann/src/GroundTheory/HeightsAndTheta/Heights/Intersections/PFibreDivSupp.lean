import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.CycDim
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsFibreDivSupp
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsFibreIncomp
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem FibreDivSupp.proof (h : FibreIncomp.Statement) : FibreDivSupp.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' n s α W hv hP' hQ hs hsQ hW W'
  have hmin : ∀ Q ∈ (P' ⊔ Ideal.span {rename v s}).minimalPrimes, IsRelevant Q → IsMultiProjPrime Q :=
    fun Q hQm hQr => ⟨hQm.1.1, cyc_isMultiHomogIdeal_of_mem_minimalPrimes hP'.2.1.2.1
      (rename_isMultiHomog hv hs) hQm, hQr⟩
  have hmem : ∀ Q ∈ (P' ⊔ Ideal.span {rename v s}).minimalPrimes, P' ≤ Q ∧ rename v s ∈ Q :=
    fun Q hQm => ⟨le_sup_left.trans hQm.1.2,
      hQm.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))⟩
  constructor
  · rintro ⟨⟨hW'p, hPW', himg⟩, hsW'⟩
    have := hW'p.1
    obtain ⟨Q, hQm, hQW'⟩ := Ideal.exists_minimalPrimes_le
      (sup_le hPW' ((Ideal.span_singleton_le_iff_mem _).2 hsW'))
    have hQr : IsRelevant Q := fun k => (hW'p.2.2 k).imp fun _ hi hq => hi (hQW' hq)
    obtain ⟨hPQ, hsQ'⟩ := hmem Q hQm
    have hQi : imageZ v Q = W := by
      have := hQm.1.1
      have hpr : (imageZ v Q).IsPrime := Ideal.comap_isPrime _ _
      have hle : imageZ v P' ⊔ Ideal.span {s} ≤ imageZ v Q :=
        sup_le (Ideal.comap_mono hPQ) ((Ideal.span_singleton_le_iff_mem _).2 hsQ')
      have hle2 : imageZ v Q ≤ W := himg ▸ Ideal.comap_mono hQW'
      exact le_antisymm hle2 (hW.1.2 ⟨hpr, hle⟩ hle2)
    have hQe := h K ι K' ι' κ v P' n s α W hv hP' hQ hs hsQ hW Q W' ⟨hmin Q hQm hQr, hPQ, hQi⟩
      ⟨hW'p, hPW', himg⟩ hQW'
    subst hQe
    exact ⟨⟨hQm, hQr⟩, hQi⟩
  · rintro ⟨⟨hW'm, hW'r⟩, himg⟩
    exact ⟨⟨hmin W' hW'm hW'r, (hmem W' hW'm).1, himg⟩, (hmem W' hW'm).2⟩

end GroundTheory.Heights₂.Heights.Inter
