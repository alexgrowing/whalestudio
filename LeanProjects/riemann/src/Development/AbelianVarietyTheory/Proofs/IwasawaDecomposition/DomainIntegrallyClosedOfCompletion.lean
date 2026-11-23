import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
open IsLocalRing GlobalTheory.Toroidal TensorProduct

namespace GlobalTheory

theorem isDomain_isIntegrallyClosed_of_adicCompletion :
    ∀ (T : Type) [CommRing T] [IsLocalRing T] [IsNoetherianRing T],
      IsDomain (AdicCompletion (maximalIdeal T) T) → IsIntegrallyClosed (AdicCompletion (maximalIdeal T) T) →
        IsDomain T ∧ IsIntegrallyClosed T := by
  intro T _ _ _ hD hI
  haveI : Module.FaithfullyFlat T (AdicCompletion (maximalIdeal T) T) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  set C := AdicCompletion (maximalIdeal T) T with hC
  set i := algebraMap T C with hi
  have hinj : Function.Injective i := FaithfulSMul.algebraMap_injective T C
  haveI hTD : IsDomain T := hinj.isDomain i
  refine ⟨hTD, ?_⟩
  set g : T →+* FractionRing C := (algebraMap C (FractionRing C)).comp i with hg
  have hginj : Function.Injective g := (IsFractionRing.injective C (FractionRing C)).comp hinj
  set φ : FractionRing T →+* FractionRing C := IsFractionRing.lift hginj with hφ
  rw [isIntegrallyClosed_iff (FractionRing T)]
  intro x hx
  obtain ⟨⟨a, ⟨b, hb⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors T) x
  have hφx : IsIntegral C (φ (IsLocalization.mk' (FractionRing T) a ⟨b, hb⟩)) := by
    refine IsIntegral.map_of_comp_eq i φ ?_ hx
    ext t
    simp [hφ, hg, IsFractionRing.lift_algebraMap]
  obtain ⟨c, hc⟩ := IsIntegrallyClosed.isIntegral_iff.mp hφx
  have hmk : φ (IsLocalization.mk' (FractionRing T) a ⟨b, hb⟩) * g b = g a := by
    rw [hφ, IsFractionRing.lift_mk']
    exact div_mul_cancel₀ _ (map_ne_zero_of_mem_nonZeroDivisors g hginj hb)
  have hcb : c * i b = i a := by
    apply IsFractionRing.injective C (FractionRing C)
    rw [map_mul, hc]
    simpa [hg] using hmk
  have ha : a ∈ Ideal.span {b} := by
    rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B := C) (Ideal.span {b}), Ideal.mem_comap,
      Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton']
    exact ⟨c, hcb⟩
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp ha
  refine ⟨d, ?_⟩
  rw [IsLocalization.eq_mk'_iff_mul_eq, ← map_mul]
  show algebraMap T (FractionRing T) (d * b) = _
  rw [hd]

end GlobalTheory
