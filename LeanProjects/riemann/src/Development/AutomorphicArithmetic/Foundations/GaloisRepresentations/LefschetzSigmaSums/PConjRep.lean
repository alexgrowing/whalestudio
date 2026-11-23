import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.HeckeTraceSemi

set_option autoImplicit false

noncomputable section

namespace UpperTheory.Gal.LocalSmoothExtension

private def Tw (_σ : ℂ ≃+* ℂ) (V : Type) : Type := V

private instance twAdd (σ : ℂ ≃+* ℂ) (V : Type) [AddCommGroup V] : AddCommGroup (Tw σ V) :=
  inferInstanceAs (AddCommGroup V)

private instance twMod (σ : ℂ ≃+* ℂ) (V : Type) [AddCommGroup V] [Module ℂ V] : Module ℂ (Tw σ V) :=
  Module.compHom V (σ.symm : ℂ →+* ℂ)

private def toTw (σ : ℂ ≃+* ℂ) (V : Type) [AddCommGroup V] : V ≃+ Tw σ V := AddEquiv.refl V

private theorem tw_smul (σ : ℂ ≃+* ℂ) (V : Type) [AddCommGroup V] [Module ℂ V] (c : ℂ) (x : V) :
    toTw σ V (c • x) = σ c • toTw σ V x := by
  change c • x = ((σ.symm : ℂ →+* ℂ) (σ c)) • x
  simp

private theorem tw_smul' (σ : ℂ ≃+* ℂ) (V : Type) [AddCommGroup V] [Module ℂ V] (c : ℂ) (x : Tw σ V) :
    c • x = toTw σ V (σ.symm c • (toTw σ V).symm x) := rfl

private theorem tw_finite (σ : ℂ ≃+* ℂ) (V : Type) [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] : FiniteDimensional ℂ (Tw σ V) := by
  let b := Module.finBasis ℂ V
  have hsm : ∀ (c : ℂ) (y : Tw σ V), (toTw σ V).symm (c • y) = σ.symm c • (toTw σ V).symm y :=
    fun c y => rfl
  let b' : Module.Basis (Fin (Module.finrank ℂ V)) ℂ (Tw σ V) := Module.Basis.ofRepr
    { toFun := fun y => Finsupp.mapRange σ (map_zero σ) (b.repr ((toTw σ V).symm y))
      invFun := fun f => toTw σ V (b.repr.symm (Finsupp.mapRange σ.symm (map_zero _) f))
      map_add' := fun x y => by
        ext i
        simp
      map_smul' := fun c y => by
        ext i
        simp [hsm]
      left_inv := fun y => by
        have hr : Finsupp.mapRange σ.symm (map_zero _)
            (Finsupp.mapRange σ (map_zero σ) (b.repr ((toTw σ V).symm y))) =
              b.repr ((toTw σ V).symm y) := by
          ext i
          simp
        simp only [hr, LinearEquiv.symm_apply_apply, AddEquiv.apply_symm_apply]
      right_inv := fun f => by
        ext i
        simp }
  exact Module.Finite.of_basis b'

private def twMap (σ : ℂ ≃+* ℂ) (V : Type) [AddCommGroup V] [Module ℂ V] (T : V →ₗ[ℂ] V) :
    Tw σ V →ₗ[ℂ] Tw σ V where
  toFun x := toTw σ V (T ((toTw σ V).symm x))
  map_add' x y := by simp
  map_smul' c x := by
    rw [RingHom.id_apply, tw_smul', tw_smul']
    simp

theorem conjRep_of : ConjRep := by
  intro σ Γ V _ _ _ _ ξ
  let ξ' : Representation ℂ Γ (Tw σ V) :=
    { toFun := fun g => twMap σ V (ξ g)
      map_one' := by
        ext x
        simp [twMap]
      map_mul' := fun g h => by
        ext x
        simp [twMap, Module.End.mul_apply] }
  exact ⟨Tw σ V, twAdd σ V, twMod σ V, tw_finite σ V, ξ', toTw σ V, tw_smul σ V, fun g x => rfl⟩

end UpperTheory.Gal.LocalSmoothExtension
