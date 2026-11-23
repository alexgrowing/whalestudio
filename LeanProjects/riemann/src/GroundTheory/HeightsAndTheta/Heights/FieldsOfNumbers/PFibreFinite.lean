import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsFibreFinite
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PContractRelDimLe
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR PFContracted

noncomputable section

universe u

theorem FibreFinite.proof : FibreFinite.Statement.{u} := by
  intro F _ K K' _ _ _ _ j ι' _ P' hP' n hP'n hPn W _ hWn _
  have := hP'.isPrime
  refine (Ideal.finite_minimalPrimes_of_isNoetherianRing _
    (P' ⊔ W.map (rename (blockIncl j ι')))).subset ?_
  rintro W' ⟨hW', hPW', hc⟩
  have := hW'.isPrime
  obtain ⟨Q, hQ, hQW'⟩ := Ideal.exists_minimalPrimes_le
    (sup_le hPW' (Ideal.map_le_iff_le_comap.mpr hc.ge))
  have := hQ.1.1
  have hP'Q : P' ≤ Q := le_sup_left.trans hQ.1.2
  suffices Q = W' by rwa [← this]
  by_contra hne
  have hQc : contractPrime j Q = W := le_antisymm (hc ▸ Ideal.comap_mono hQW')
    (Ideal.le_comap_map.trans (Ideal.comap_mono (le_sup_right.trans hQ.1.2)))
  have hne' : P' ≠ Q := by
    rintro rfl
    rw [hQc, hWn] at hPn
    simp only [natCast_withBot_withTop] at hPn
    have := WithTop.coe_inj.mp (WithBot.coe_inj.mp hPn)
    omega
  obtain ⟨f, hfQ, hfP⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hP'Q hne')
  obtain ⟨g, hgW, hgQ⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hQW' hne)
  have h1 := ringKrullDim_add_one_le hP'Q hfP hfQ
  have h2 := ringKrullDim_add_one_le hQW' hgQ hgW
  obtain ⟨D, -, hD⟩ := exists_ringKrullDim_eq
    (fun T _ hq => killBlocks_mem_of_isMultiHomogIdeal hP'.multiHomog T hq) hP'.relevant
  obtain ⟨E, -, hE⟩ := exists_ringKrullDim_eq
    (fun T _ hq => killBlocks_mem_of_isMultiHomogIdeal hW'.multiHomog T hq) hW'.relevant
  have h3 := ContractRelDimLe.proof F K K' j ι' W' hW'
  rw [hc, hWn, relDim_eq_int hE, natCast_withBot_withTop] at h3
  rw [relDim_eq_int hD, natCast_withBot_withTop] at hP'n
  have h4 : ((E + 1 + 1 : ℕ) : WithBot ℕ∞) ≤ D := by
    rw [← hD]
    rw [hE] at h2
    push_cast
    exact le_trans (by gcongr) h1
  have h3' : (n : ℤ) ≤ E - Fintype.card K' := by exact_mod_cast h3
  have hP'n' : (D : ℤ) - Fintype.card K' = (n + 1 : ℕ) := by exact_mod_cast hP'n
  have h4' : E + 1 + 1 ≤ D := by exact_mod_cast h4
  omega

end

end GroundTheory.Heights₂.Heights.FieldNumbers
