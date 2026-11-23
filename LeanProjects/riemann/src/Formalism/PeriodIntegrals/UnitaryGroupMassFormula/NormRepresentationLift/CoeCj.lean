import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationLift.ActsByFrameAct

noncomputable section

open scoped Classical

namespace PI.NRL

open NumberField IsDedekindDomain

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem star_int (x : 𝓞 E) : ∃ y : 𝓞 E, (y : E) = star (x : E) := by
  have h : IsIntegral ℤ (star (x : E)) := by
    have := (RingOfIntegers.isIntegral_coe x).map (starRingEnd E).toIntAlgHom
    exact this
  exact ⟨⟨star (x : E), h⟩, rfl⟩

def cj (x : 𝓞 E) : 𝓞 E := Classical.choose (star_int x)

@[simp] theorem coe_cj (x : 𝓞 E) : ((cj x : 𝓞 E) : E) = star (x : E) := Classical.choose_spec (star_int x)

theorem cj_cj (x : 𝓞 E) : cj (cj x) = x := by
  apply RingOfIntegers.ext; simp

theorem exists_beta (P : HeightOneSpectrum (𝓞 E)) :
    ∃ β : E, (∀ p ∈ P.asIdeal, ∃ o : 𝓞 E, β * (p : E) = (o : E)) ∧
      ∀ s : 𝓞 E, s ∉ P.asIdeal → ∀ o : 𝓞 E, (s : E) * β ≠ (o : E) := by
  have hP0 : (P.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr P.ne_bot
  have hnot : ¬ ((P.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)⁻¹ ≤ 1) := by
    intro hle
    have h1 : (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ≤ P.asIdeal := by
      calc (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)
          = P.asIdeal * (P.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)⁻¹ :=
            (mul_inv_cancel₀ hP0).symm
        _ ≤ P.asIdeal * 1 := mul_le_mul_right hle _
        _ = P.asIdeal := mul_one _
    rw [← FractionalIdeal.coeIdeal_top, FractionalIdeal.coeIdeal_le_coeIdeal] at h1
    exact P.isPrime.ne_top (top_le_iff.mp h1)
  obtain ⟨β, hβ, hβ1⟩ := Set.not_subset.mp hnot
  have hmem := (FractionalIdeal.mem_inv_iff hP0).mp hβ
  have hPO : ∀ p ∈ P.asIdeal, ∃ o : 𝓞 E, β * (p : E) = (o : E) := by
    intro p hp
    obtain ⟨o, ho⟩ := (FractionalIdeal.mem_one_iff _).mp
      (hmem _ (FractionalIdeal.mem_coeIdeal_of_mem _ hp))
    exact ⟨o, ho.symm⟩
  refine ⟨β, hPO, fun s hs o ho => hβ1 ?_⟩
  obtain ⟨y, i, hi, hyi⟩ := P.isMaximal.exists_inv hs
  obtain ⟨o', ho'⟩ := hPO i hi
  refine (FractionalIdeal.mem_one_iff _).mpr ⟨y * o + o', ?_⟩
  have : β = (y : E) * ((s : E) * β) + β * (i : E) := by
    have h1 : ((y * s + i : 𝓞 E) : E) = 1 := by rw [hyi]; simp
    push_cast at h1
    linear_combination (-β) * h1
  rw [this, ho, ho']
  rw [map_add, map_mul]

end PI.NRL
