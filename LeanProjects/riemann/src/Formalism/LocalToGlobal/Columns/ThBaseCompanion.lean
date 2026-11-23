import Formalism.LocalToGlobal.Columns.RecLevelLocT

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] {ST : Finset (Pl E)} {π : 𝓞 E}

theorem th_base_companion (h : BasePi ST π) (pb : 𝓞 E) (hpb : algebraMap (𝓞 E) E pb = star (algebraMap (𝓞 E) E π)) :
    baseLb E n ST ⊔ Ideal.span {pb} • Submodule.span (𝓞 E)
      (dualSet (hc.sig : E →+* E) (1 : Matrix (Fin n) (Fin n) E) (baseLb E n ST)) = stdLat E n := by
  have e : Submodule.span (𝓞 E) (dualSet (hc.sig : E →+* E) (1 : Matrix (Fin n) (Fin n) E) (baseLb E n ST)) =
      rll_dLat n (star (algebraMap (𝓞 E) E π)) := rll_baseDual_eq hc n h
  rw [e]
  apply le_antisymm
  · refine sup_le (rll_baseLb_le n ST) ?_
    rw [Submodule.smul_le]
    intro r hr m hm
    obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton'.1 hr
    obtain ⟨h1, h2⟩ := (rll_mem_dLat n _ m).1 hm
    rw [mem_stdLat]
    intro i
    by_cases hi : i = lastIdx n
    · subst hi
      obtain ⟨t, ht⟩ := h2
      refine ⟨s * t, ?_⟩
      rw [map_mul, ht, Pi.smul_apply, Algebra.smul_def, map_mul, hpb, mul_assoc]
    · obtain ⟨t, ht⟩ := h1 i hi
      refine ⟨s * pb * t, ?_⟩
      rw [map_mul, ht, Pi.smul_apply, Algebra.smul_def]
  · intro x hx
    rw [mem_stdLat] at hx
    choose r hr using hx
    have hs0 : star (algebraMap (𝓞 E) E π) ≠ 0 := h.star_ne_zero
    have e1 : x = (x - Pi.single (lastIdx n) (x (lastIdx n))) +
        pb • (Pi.single (lastIdx n) ((star (algebraMap (𝓞 E) E π))⁻¹ * x (lastIdx n)) : Fin n → E) := by
      funext i
      by_cases hi : i = lastIdx n
      · subst hi
        simp only [Pi.add_apply, Pi.sub_apply, Pi.single_eq_same, Pi.smul_apply, sub_self, zero_add]
        rw [Algebra.smul_def, hpb, mul_inv_cancel_left₀ hs0]
      · simp only [Pi.add_apply, Pi.sub_apply, Pi.single_eq_of_ne hi, Pi.smul_apply, sub_zero, smul_zero, add_zero]
    rw [e1]
    refine Submodule.add_mem_sup ?_ (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self pb) ?_)
    · rw [rll_baseLb_eq n h, rll_mem_dLat]
      refine ⟨fun i hi => ?_, ?_⟩
      · rw [Pi.sub_apply, Pi.single_eq_of_ne hi, sub_zero]
        exact ⟨r i, hr i⟩
      · rw [Pi.sub_apply, Pi.single_eq_same, sub_self, mul_zero]
        exact zero_mem _
    · rw [rll_mem_dLat]
      refine ⟨fun i hi => ?_, ?_⟩
      · rw [Pi.single_eq_of_ne hi]
        exact zero_mem _
      · rw [Pi.single_eq_same, mul_inv_cancel_left₀ hs0]
        exact ⟨r _, hr _⟩

end Formalism.L2.Col
