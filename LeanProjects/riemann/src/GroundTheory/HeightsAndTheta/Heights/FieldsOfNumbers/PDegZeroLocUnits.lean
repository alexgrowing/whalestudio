import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsDegZeroLocUnits
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsSemilocalLengthSum
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDegZeroLocQuot
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

theorem DegZeroLocUnits.proof : DegZeroLocUnits.Statement.{u} := by
  intro F _ K _ _ ι _ P hP 𝒲 h𝒲ne h𝒲
  have := hP.isPrime
  have hne : ∀ g : MRing ι F, g ∉ P →
      algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P g) ≠ 0 :=
    fun g hg => by
      rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
      exact hg
  intro x hx
  constructor
  · rintro ⟨y, hy, hxy⟩ W hW
    exact ⟨y, degZeroLoc_anti P (Set.singleton_subset_iff.mpr hW) hy, hxy⟩
  · intro h
    obtain ⟨b, f, g, hf, hg, hgP, hgW, hx'⟩ :=
      DegZeroLocQuot.proof F K ι P 𝒲 (fun W hW => (h𝒲 W hW).1.isPrime) x hx
    by_cases hfW : ∃ W ∈ 𝒲, f ∈ W
    ·
      exfalso
      obtain ⟨W, hW, hfW⟩ := hfW
      have hWp : W.IsPrime := (h𝒲 W hW).1.isPrime
      obtain ⟨y, hy, hxy⟩ := h W hW
      obtain ⟨b', f', g', -, -, hg'P, hg'W, hy'⟩ := DegZeroLocQuot.proof F K ι P {W}
        (fun W' hW' => by rw [Set.mem_singleton_iff.mp hW']; exact hWp) y hy
      rw [hx', hy', div_mul_div_comm,
        div_eq_one_iff_eq (mul_ne_zero (hne g hgP) (hne g' hg'P)), ← map_mul, ← map_mul,
        ← map_mul, ← map_mul] at hxy
      have h2 := Ideal.Quotient.eq.mp (IsFractionRing.injective _ _ hxy)
      have h3 : g * g' ∈ W := by
        have := W.sub_mem (W.mul_mem_right f' hfW) ((h𝒲 W hW).2 h2)
        rwa [sub_sub_cancel] at this
      rcases hWp.mem_or_mem h3 with h4 | h4
      exacts [hgW W hW h4, hg'W W (Set.mem_singleton W) h4]
    ·
      push Not at hfW
      obtain ⟨W₀, hW₀⟩ := h𝒲ne
      have hfP : f ∉ P := fun h' => hfW W₀ hW₀ ((h𝒲 W₀ hW₀).2 h')
      refine ⟨_, div_mem_degZeroLoc P 𝒲 hg hf hfP hfW, ?_⟩
      rw [hx', div_mul_div_comm, mul_comm (algebraMap _ _ _),
        div_self (mul_ne_zero (hne g hgP) (hne f hfP))]

end

end GroundTheory.Heights₂.Heights.FieldNumbers
