import Mathlib
import GroundTheory.LocalFields.LocalArtinUniqueness
import GroundTheory.LocalFields.LocalArtinCompletion
import GroundTheory.LocalFields.LocalArtinFunctoriality
import GroundTheory.LocalFields.LocalArtinTransport

noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel

section Main

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (Ω : Type*) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

theorem localArtinMap_spec :
    Continuous (localArtinMap K Ω) ∧
      (∀ π : Kˣ, ord (π : K) = 1 →
        restrictAb (maximalUnramifiedExtension K Ω) maximalUnramifiedExtension_le_maximalAbelianExtension
          (localArtinMap K Ω π) = maximalUnramifiedExtensionFrobenius K Ω) ∧
      ∀ (L : IntermediateField K Ω) [FiniteDimensional K L] [IsAbelianGalois K L],
        ((restrictAb L (le_maximalAbelianExtension L)).comp (localArtinMap K Ω)).ker =
            (normUnits K L).range ∧
          Function.Surjective ((restrictAb L (le_maximalAbelianExtension L)).comp (localArtinMap K Ω)) :=
  ⟨continuous_localArtinMap, fun _ hπ => restrictAb_localArtinMap_uniformizer hπ,
    fun L _ _ => ⟨ker_restrictAb_localArtinMap L, surjective_restrictAb_localArtinMap L⟩⟩

theorem localArtinMap_unramified (L : IntermediateField K Ω) (hL : IsUnramifiedSubextension L)
    (x : Kˣ) :
    have := hL.1
    have := hL.isGalois
    restrictAb L (hL.le_maximalUnramifiedExtension.trans maximalUnramifiedExtension_le_maximalAbelianExtension)
      (localArtinMap K Ω x) = unramifiedFrobenius K Ω L ^ ord (x : K) :=
  have := hL.1
  have := hL.isGalois
  restrictAb_localArtinMap_of_le_maximalUnramifiedExtension L hL.le_maximalUnramifiedExtension x

end Main

section Functoriality

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {K' : Type*} [Field K'] [ValuativeRel K'] [TopologicalSpace K'] [IsNonarchimedeanLocalField K']

theorem isSepClosure_of_isSeparable (K K' Ω : Type*) [Field K] [Field K'] [Field Ω] [Algebra K K']
    [Algebra K Ω] [Algebra K' Ω] [IsScalarTower K K' Ω] [Algebra.IsSeparable K K'] [IsSepClosure K' Ω] :
    IsSepClosure K Ω :=
  ⟨IsSepClosure.sep_closed K', Algebra.IsSeparable.trans K K' Ω⟩

theorem localArtinMap_norm [Algebra K K'] [ValuativeExtension K K'] [FiniteDimensional K K']
    [Algebra.IsSeparable K K'] {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra K' Ω]
    [IsScalarTower K K' Ω] [IsSepClosure K' Ω] (x : K'ˣ) {y : Ω} :
    have := isSepClosure_of_isSeparable K K' Ω
    ∀ hy : y ∈ maximalAbelianExtension K Ω,
      ((localArtinMap K' Ω x ⟨y, maximalAbelianExtension_le_of_algebra hy⟩ :
        maximalAbelianExtension K' Ω) : Ω) =
        ((localArtinMap K Ω (normUnits K K' x) ⟨y, hy⟩ : maximalAbelianExtension K Ω) : Ω) := by
  intro _ hy
  exact localArtinMap_apply_of_algebra x hy

theorem localArtinMap_transport {Ω Ω' : Type*} [Field Ω] [Field Ω'] [Algebra K Ω] [Algebra K' Ω']
    [IsSepClosure K Ω] [IsSepClosure K' Ω'] (e : K ≃+* K') (he : ∀ x y : K, e x ≤ᵥ e y ↔ x ≤ᵥ y)
    (ε : Ω ≃+* Ω') (hε : ∀ x : K, ε (algebraMap K Ω x) = algebraMap K' Ω' (e x)) (x : Kˣ) {y : Ω}
    (hy : y ∈ maximalAbelianExtension K Ω) :
    ε ((localArtinMap K Ω x ⟨y, hy⟩ : maximalAbelianExtension K Ω) : Ω) =
      ((localArtinMap K' Ω' (Units.map e.toRingHom.toMonoidHom x)
        ⟨ε y, (mem_maximalAbelianExtension_transport_iff e ε hε).2 hy⟩ :
          maximalAbelianExtension K' Ω') : Ω') :=
  transport_localArtinMap_apply e he ε hε x hy

end Functoriality

end GroundTheory.LocalField
