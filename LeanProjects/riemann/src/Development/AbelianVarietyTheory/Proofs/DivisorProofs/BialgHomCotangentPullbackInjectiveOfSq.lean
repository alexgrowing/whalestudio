import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero
open scoped TensorProduct

namespace GlobalTheory

namespace PDiv

theorem cotMap_injective_of_sq : ∀ (R C A : Type) [CommRing R] [CommRing C] [CommRing A]
    [Bialgebra R C] [Bialgebra R A] (f : C →ₐc[R] A),
    (∀ b : C, f b ∈ RingHom.ker (Bialgebra.counitAlgHom R A) ^ 2 →
      b ∈ RingHom.ker (Bialgebra.counitAlgHom R C) ^ 2) →
    Function.Injective (GlobalTheory.PDiv.cotMap f) := by
  intro R C A _ _ _ _ _ f h
  rw [injective_iff_map_eq_zero]
  intro w hw
  obtain ⟨c, rfl⟩ := AugCot.d_surjective _ w
  have hw' : dUnit R (f c) = 0 := (cotMap_d f c).symm.trans hw
  rw [dUnit, AugCot.d_eq_zero_iff] at hw'
  change AugCot.d _ c = 0
  rw [AugCot.d_eq_zero_iff]
  apply h
  have e : Bialgebra.counitAlgHom R A (f c) = Bialgebra.counitAlgHom R C c :=
    AlgHom.congr_fun (BialgHomClass.counitAlgHom_comp f) c
  have e2 : f (c - algebraMap R C (Bialgebra.counitAlgHom R C c)) =
      f c - algebraMap R A (Bialgebra.counitAlgHom R A (f c)) := by
    rw [map_sub, e]
    congr 1
    exact AlgHom.commutes (f : C →ₐ[R] A) _
  rw [e2]
  exact hw'

end PDiv

end GlobalTheory
