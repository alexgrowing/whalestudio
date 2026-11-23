import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelCore

noncomputable section

open NumberField

namespace Formalism.L2.S.Pv.DdTraceCore

theorem relTrace_mem_inv_different (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (y : E)
    (hy : ∀ d ∈ differentIdeal ℤ (𝓞 F), ∃ a : 𝓞 E, algebraMap (𝓞 E) E a = y * algebraMap F E (d : F))
    (o : 𝓞 E) :
    Algebra.trace F E ((o : E) * y) ∈
      ((differentIdeal ℤ (𝓞 F) : FractionalIdeal (nonZeroDivisors (𝓞 F)) F))⁻¹ := by
  have hD : ((differentIdeal ℤ (𝓞 F) : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr differentIdeal_ne_bot
  rw [FractionalIdeal.mem_inv_iff hD]
  intro x hx
  obtain ⟨d, hd, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp hx
  obtain ⟨a, ha⟩ := hy d hd
  rw [FractionalIdeal.mem_one_iff]
  have key : Algebra.trace F E ((o : E) * y) * algebraMap (𝓞 F) F d =
      Algebra.trace F E (algebraMap (𝓞 E) E (o * a)) := by
    rw [map_mul (algebraMap (𝓞 E) E), ha]
    change _ = Algebra.trace F E ((o : E) * (y * algebraMap F E (d : F)))
    rw [← mul_assoc]
    generalize (o : E) * y = z
    have h := (Algebra.trace F E).map_smul (d : F) z
    rw [Algebra.smul_def, smul_eq_mul] at h
    rw [mul_comm z, h, mul_comm]
  have hint : IsIntegral ℤ (Algebra.trace F E (algebraMap (𝓞 E) E (o * a))) :=
    Algebra.isIntegral_trace (RingOfIntegers.isIntegral_coe (o * a))
  exact ⟨⟨_, hint⟩, key.symm⟩

theorem ddTraceCore_holds : Formalism.L2.SG.Pf.DdTraceCore := by
  intro F E _ _ _ _ _ y hy o
  have hinj : Function.Injective (algebraMap (𝓞 F) (𝓞 E)) :=
    FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E)
  have hne : ((Ideal.map (algebraMap (𝓞 F) (𝓞 E)) (differentIdeal ℤ (𝓞 F)) :
      Ideal (𝓞 E)) : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ≠ 0 := by
    rw [FractionalIdeal.coeIdeal_ne_zero, ne_eq, Ideal.map_eq_bot_iff_of_injective hinj]
    exact differentIdeal_ne_bot
  have hyF : ∀ d ∈ differentIdeal ℤ (𝓞 F),
      ∃ a : 𝓞 E, algebraMap (𝓞 E) E a = y * algebraMap F E (d : F) := by
    intro d hd
    have hmem : algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) d) ∈
        ((Ideal.map (algebraMap (𝓞 F) (𝓞 E)) (differentIdeal ℤ (𝓞 F)) :
          Ideal (𝓞 E)) : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) :=
      (FractionalIdeal.mem_coeIdeal _).mpr ⟨_, Ideal.mem_map_of_mem _ hd, rfl⟩
    obtain ⟨a, ha⟩ := (FractionalIdeal.mem_one_iff _).mp ((FractionalIdeal.mem_inv_iff hne).mp hy _ hmem)
    exact ⟨a, ha⟩
  have h1 := relTrace_mem_inv_different F E y hyF o
  have h10 : (1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ≠ 0 :=
    @one_ne_zero (FractionalIdeal (nonZeroDivisors (𝓞 F)) F) _ _ _
  rw [coeIdeal_differentIdeal (K := ℚ), inv_inv, FractionalIdeal.mem_dual h10] at h1
  obtain ⟨m, hm⟩ := h1 1 (FractionalIdeal.one_mem_one _)
  refine ⟨m, ?_⟩
  rw [← Algebra.trace_trace (S := F)]
  rw [Algebra.traceForm_apply, mul_one] at hm
  rw [← hm]
  rfl

end Formalism.L2.S.Pv.DdTraceCore
