import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsDegZeroLocSeparate
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDegZeroLocQuot
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.RelevantMinimalOfDivCycleNeZero
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

theorem DegZeroLocSeparate.proof : DegZeroLocSeparate.Statement.{u} := by
  intro F _ K _ _ ι _ P hP 𝒲 h𝒲 h𝒲P
  have := hP.isPrime
  intro W₁ hW₁ W₂ hW₂ hle
  obtain ⟨hW₁p, hPW₁⟩ := h𝒲P W₁ hW₁
  obtain ⟨hW₂p, hPW₂⟩ := h𝒲P W₂ hW₂
  have : W₂.IsPrime := hW₂p.isPrime

  obtain ⟨f, c, hf, hfW₁, hfW₂⟩ := exists_form_mem_not_mem hW₁p.multiHomog hle

  obtain ⟨e, h, hh, hce, hhS⟩ := exists_form_avoid_primes (insert P h𝒲.toFinset)
    (fun W hW => by
      rcases Finset.mem_insert.mp hW with rfl | hW
      · exact ⟨hP.isPrime, hP.multiHomog, hP.relevant⟩
      · have hW' := (h𝒲P W (h𝒲.mem_toFinset.mp hW)).1
        exact ⟨hW'.isPrime, hW'.multiHomog, hW'.relevant⟩) c
  have hhP : h ∉ P := hhS P (Finset.mem_insert_self _ _)
  have hh𝒲 : ∀ W ∈ 𝒲, h ∉ W := fun W hW =>
    hhS W (Finset.mem_insert_of_mem (h𝒲.mem_toFinset.mpr hW))

  obtain ⟨m, hm, hmW₂⟩ := exists_form_not_mem_of_isRelevant (H := W₂) hW₂p.relevant (e - c)
  have hfm : IsMultiHomog (f * m) e := by
    have := IsWeightedHomogeneous.mul hf hm
    rwa [add_tsub_cancel_of_le hce] at this
  have hfmW₂ : f * m ∉ W₂ := fun h' => (hW₂p.isPrime.mem_or_mem h').elim hfW₂ hmW₂
  have hfmP : f * m ∉ P := fun h' => hfmW₂ (hPW₂ h')
  have hq0 : ∀ a : MRing ι F, a ∉ P →
      algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P a) ≠ 0 :=
    fun a ha => by
      rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
      exact ha
  refine ⟨_, div_mem_degZeroLoc P 𝒲 hfm hh hhP hh𝒲, ?_, _,
    div_mem_degZeroLoc P {W₂} hh hfm hfmP
      (fun W hW => by rw [Set.mem_singleton_iff.mp hW]; exact hfmW₂), ?_⟩
  ·
    rintro ⟨y, hy, hxy⟩
    obtain ⟨b', f', g', -, -, hg'P, hg'W, hy'⟩ := DegZeroLocQuot.proof F K ι P {W₁}
      (fun W hW => by rw [Set.mem_singleton_iff.mp hW]; exact hW₁p.isPrime) y hy
    rw [hy', div_mul_div_comm, div_eq_one_iff_eq (mul_ne_zero (hq0 h hhP) (hq0 g' hg'P)),
      ← map_mul, ← map_mul, ← map_mul, ← map_mul] at hxy
    have h2 := Ideal.Quotient.eq.mp (IsFractionRing.injective _ _ hxy)
    have h3 : h * g' ∈ W₁ := by
      have := W₁.sub_mem (W₁.mul_mem_right f' (W₁.mul_mem_right m hfW₁)) (hPW₁ h2)
      rwa [sub_sub_cancel] at this
    rcases hW₁p.isPrime.mem_or_mem h3 with h4 | h4
    exacts [hh𝒲 W₁ hW₁ h4, hg'W W₁ (Set.mem_singleton W₁) h4]
  ·
    rw [div_mul_div_comm, mul_comm (algebraMap _ _ (Ideal.Quotient.mk P (f * m))),
      div_self (mul_ne_zero (hq0 h hhP) (hq0 _ hfmP))]

end

end GroundTheory.Heights₂.Heights.FieldNumbers
