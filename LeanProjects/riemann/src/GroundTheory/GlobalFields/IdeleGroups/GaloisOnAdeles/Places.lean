import Mathlib
import GroundTheory.GlobalFields.IdeleGroups.GaloisOnAdeles.Action
import GroundTheory.GlobalFields.SemilocalAlgebras.Galois

namespace GroundTheory.Global

open IsDedekindDomain NumberField
open scoped NumberField.AdeleRing NumberField.LiesOver

noncomputable section

namespace AdeleBaseChange

variable {L L' : Type*} [Field L] [NumberField L] [Field L'] [NumberField L'] [Algebra L L']

theorem adeleRingEquiv_eq_adeleMap (τ : L ≃+* L') (hτ : ∀ l, τ l = algebraMap L L' l) :
    (adeleRingEquiv τ : 𝔸[L] →+* 𝔸[L']) = adeleMap L L' := by
  refine adeleRingHom_ext_rat (fun l ↦ ?_) (fun a ↦ ?_)
  · rw [RingHom.coe_coe, adeleRingEquiv_algebraMap, adeleMap_algebraMap, hτ]
  · rw [RingHom.coe_coe, adeleRingEquiv_adeleMap_rat, adeleMap_adeleMap]

theorem adeleRingEquiv_snd (τ : L ≃+* L') (hτ : ∀ l, τ l = algebraMap L L' l) (x : 𝔸[L])
    (w' : HeightOneSpectrum (𝓞 L')) :
    (adeleRingEquiv τ x).2 w' = SemiLocal.completionMap (below L w') w' (x.2 (below L w')) := by
  rw [← RingHom.coe_coe, adeleRingEquiv_eq_adeleMap τ hτ]
  rfl

theorem adeleRingEquiv_fst (τ : L ≃+* L') (hτ : ∀ l, τ l = algebraMap L L' l) (x : 𝔸[L])
    (w' : InfinitePlace L') :
    (adeleRingEquiv τ x).1 w' =
      algebraMap (w'.comap (algebraMap L L')).Completion w'.Completion
        (x.1 (w'.comap (algebraMap L L'))) := by
  rw [← RingHom.coe_coe, adeleRingEquiv_eq_adeleMap τ hτ]
  rfl

theorem completionMap_below_algebraMap (τ : L ≃+* L') (hτ : ∀ l, τ l = algebraMap L L' l)
    (w' : HeightOneSpectrum (𝓞 L')) (l : L) :
    SemiLocal.completionMap (below L w') w' (algebraMap L ((below L w').adicCompletion L) l) =
      algebraMap L' (w'.adicCompletion L') (τ l) := by
  rw [SemiLocal.completionMap_algebraMap, hτ, IsScalarTower.algebraMap_apply L L']

omit [NumberField L] [NumberField L'] in

theorem completion_algebraMap_comap_apply (τ : L ≃+* L') (hτ : ∀ l, τ l = algebraMap L L' l)
    (w' : InfinitePlace L') (l : L) :
    algebraMap (w'.comap (algebraMap L L')).Completion w'.Completion
        (algebraMap L (w'.comap (algebraMap L L')).Completion l) =
      algebraMap L' w'.Completion (τ l) := by
  rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply L L', hτ]

variable {M M' : Type*} [Field M] [NumberField M] [Field M'] [NumberField M']

def comapPrime (τ : M ≃+* M') (w' : HeightOneSpectrum (𝓞 M')) : HeightOneSpectrum (𝓞 M) :=
  letI : Algebra M M' := (τ : M →+* M').toAlgebra
  below M w'

omit [NumberField M] [NumberField M'] in
theorem comapPrime_asIdeal (τ : M ≃+* M') (w' : HeightOneSpectrum (𝓞 M')) :
    (comapPrime τ w').asIdeal = w'.asIdeal.comap (RingOfIntegers.mapRingHom (τ : M →+* M')) :=
  rfl

def finiteCompletionMap (τ : M ≃+* M') (w' : HeightOneSpectrum (𝓞 M')) :
    (comapPrime τ w').adicCompletion M →+* w'.adicCompletion M' :=
  letI : Algebra M M' := (τ : M →+* M').toAlgebra
  SemiLocal.completionMap (below M w') w'

theorem finiteCompletionMap_algebraMap (τ : M ≃+* M') (w' : HeightOneSpectrum (𝓞 M')) (l : M) :
    finiteCompletionMap τ w' (algebraMap M _ l) = algebraMap M' (w'.adicCompletion M') (τ l) :=
  letI : Algebra M M' := (τ : M →+* M').toAlgebra
  completionMap_below_algebraMap τ (fun _ ↦ rfl) w' l

def infiniteCompletionMap (τ : M ≃+* M') (w' : InfinitePlace M') :
    (w'.comap (τ : M →+* M')).Completion →+* w'.Completion :=
  letI : Algebra M M' := (τ : M →+* M').toAlgebra
  algebraMap (w'.comap (algebraMap M M')).Completion w'.Completion

omit [NumberField M] [NumberField M'] in

theorem infiniteCompletionMap_algebraMap (τ : M ≃+* M') (w' : InfinitePlace M') (l : M) :
    infiniteCompletionMap τ w' (algebraMap M _ l) = algebraMap M' w'.Completion (τ l) :=
  letI : Algebra M M' := (τ : M →+* M').toAlgebra
  completion_algebraMap_comap_apply τ (fun _ ↦ rfl) w' l

theorem adeleRingEquiv_snd_eq (τ : M ≃+* M') (x : 𝔸[M]) (w' : HeightOneSpectrum (𝓞 M')) :
    (adeleRingEquiv τ x).2 w' = finiteCompletionMap τ w' (x.2 (comapPrime τ w')) :=
  letI : Algebra M M' := (τ : M →+* M').toAlgebra
  adeleRingEquiv_snd τ (fun _ ↦ rfl) x w'

theorem adeleRingEquiv_fst_eq (τ : M ≃+* M') (x : 𝔸[M]) (w' : InfinitePlace M') :
    (adeleRingEquiv τ x).1 w' = infiniteCompletionMap τ w' (x.1 (w'.comap (τ : M →+* M'))) :=
  letI : Algebra M M' := (τ : M →+* M').toAlgebra
  adeleRingEquiv_fst τ (fun _ ↦ rfl) x w'

section Galois

variable {K : Type*} [Field K] [NumberField K] [Algebra K M]

omit [NumberField K] [NumberField M] in

theorem comapPrime_eq_inv_smul (σ : M ≃ₐ[K] M) (w' : HeightOneSpectrum (𝓞 M)) :
    comapPrime (σ : M ≃+* M) w' = σ⁻¹ • w' := by
  ext1
  rw [comapPrime_asIdeal, SemiLocal.smul_asIdeal, Ideal.pointwise_smul_eq_comap]
  ext y
  simp only [Ideal.mem_comap]
  constructor <;> intro h <;> convert h using 2 <;> ext <;> rfl

omit [NumberField K] [NumberField M] in

theorem comap_eq_inv_smul (σ : M ≃ₐ[K] M) (w' : InfinitePlace M) :
    w'.comap ((σ : M ≃+* M) : M →+* M) = σ⁻¹ • w' := by
  ext y
  rw [InfinitePlace.comap_apply, InfinitePlace.smul_apply]
  rfl

omit [NumberField K] in

theorem smul_snd (σ : M ≃ₐ[K] M) (x : 𝔸[M]) (w' : HeightOneSpectrum (𝓞 M)) :
    (σ • x).2 w' = finiteCompletionMap (σ : M ≃+* M) w' (x.2 (comapPrime (σ : M ≃+* M) w')) :=
  adeleRingEquiv_snd_eq _ x w'

omit [NumberField K] in

theorem smul_fst (σ : M ≃ₐ[K] M) (x : 𝔸[M]) (w' : InfinitePlace M) :
    (σ • x).1 w' = infiniteCompletionMap (σ : M ≃+* M) w' (x.1 (w'.comap ((σ : M ≃+* M) : M →+* M))) :=
  adeleRingEquiv_fst_eq _ x w'

end Galois

end AdeleBaseChange

end

end GroundTheory.Global
