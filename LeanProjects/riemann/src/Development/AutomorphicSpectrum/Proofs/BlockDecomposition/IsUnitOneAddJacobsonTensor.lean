import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.JacUnit

theorem main (O O' R : Type) [CommRing O] [CommRing O'] [Algebra O O'] [Module.Finite O O'] [CommRing R] [Algebra O R] (x : O' ⊗[O] R) (hx : x ∈ Ideal.map (Algebra.TensorProduct.includeRight : R →ₐ[O] O' ⊗[O] R) (⊥ : Ideal R).jacobson) : IsUnit (1 + x) := by
  classical
  letI : Algebra R (O' ⊗[O] R) := (Algebra.TensorProduct.includeRight : R →ₐ[O] O' ⊗[O] R).toRingHom.toAlgebra
  have hint : Algebra.IsIntegral R (O' ⊗[O] R) := by
    let e : (R ⊗[O] O') ≃ₐ[O] (O' ⊗[O] R) := Algebra.TensorProduct.comm O R O'
    have hfin : (algebraMap R (R ⊗[O] O')).Finite := by
      rw [RingHom.finite_algebraMap]
      infer_instance
    have hcomp : (algebraMap R (O' ⊗[O] R)) = (e : (R ⊗[O] O') →+* (O' ⊗[O] R)).comp (algebraMap R (R ⊗[O] O')) := by
      ext r
      simp [e, RingHom.algebraMap_toAlgebra]
    have hf2 : (algebraMap R (O' ⊗[O] R)).Finite := by
      rw [hcomp]
      exact RingHom.Finite.comp (RingHom.Finite.of_surjective _ e.surjective) hfin
    exact ⟨fun y => (hf2.to_isIntegral) y⟩
  have hle : Ideal.map (algebraMap R (O' ⊗[O] R)) (⊥ : Ideal R).jacobson ≤ (⊥ : Ideal (O' ⊗[O] R)).jacobson := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    rw [Ideal.mem_comap, Ideal.jacobson, Submodule.mem_sInf]
    rintro m ⟨-, hm⟩
    have hc : (Ideal.comap (algebraMap R (O' ⊗[O] R)) m).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal m
    rw [← Ideal.mem_comap]
    exact (sInf_le (show _ ∈ {J : Ideal R | (⊥ : Ideal R) ≤ J ∧ J.IsMaximal} from ⟨bot_le, hc⟩) : (⊥ : Ideal R).jacobson ≤ _) hr
  have hx' : x ∈ (⊥ : Ideal (O' ⊗[O] R)).jacobson := hle hx
  have := Ideal.mem_jacobson_bot.1 hx' 1
  simpa [mul_one, add_comm] using this

end GlobalTheory.CompanionTheory.JacUnit
