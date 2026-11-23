import Mathlib
import GroundTheory.ProfiniteCohomology.RestrictedRamification.LocalMaps
import GroundTheory.ProfiniteCohomology.RestrictedRamification.IsUnramifiedOutsideIffLeMaxUnramifiedOutside
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open NumberField IsDedekindDomain

noncomputable section

universe u

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  {S T U : Set (HeightOneSpectrum (𝓞 K))}

def gsAutExtend (S : Set (HeightOneSpectrum (𝓞 K))) (σ : galUnramifiedOutside K Ω S) : Gal(Ω/K) :=
  (AlgEquiv.restrictNormalHom_surjective (K₁ := maxUnramifiedOutside K Ω S) Ω σ).choose

theorem gsAutExtend_apply (σ : galUnramifiedOutside K Ω S) (y : maxUnramifiedOutside K Ω S) :
    gsAutExtend S σ (y : Ω) = ((σ y : maxUnramifiedOutside K Ω S) : Ω) := by
  have h := (AlgEquiv.restrictNormalHom_surjective (K₁ := maxUnramifiedOutside K Ω S) Ω σ).choose_spec
  conv_rhs => rw [← h]
  exact (AlgEquiv.restrictNormal_commutes (gsAutExtend S σ) (maxUnramifiedOutside K Ω S) y).symm

def gsResFun (T : Set (HeightOneSpectrum (𝓞 K))) (σ : galUnramifiedOutside K Ω S) :
    galUnramifiedOutside K Ω T :=
  AlgEquiv.restrictNormalHom (maxUnramifiedOutside K Ω T) (gsAutExtend S σ)

theorem gsResFun_apply (h : T ⊆ S) (σ : galUnramifiedOutside K Ω S) (x : maxUnramifiedOutside K Ω T) :
    ((gsResFun T σ x : maxUnramifiedOutside K Ω T) : Ω) =
      ((σ ⟨x, maxUnramifiedOutside_mono h x.2⟩ : maxUnramifiedOutside K Ω S) : Ω) := by
  rw [gsResFun, AlgEquiv.restrictNormalHom_apply]
  exact gsAutExtend_apply σ ⟨x, maxUnramifiedOutside_mono h x.2⟩

def gsRes (h : T ⊆ S) : galUnramifiedOutside K Ω S →* galUnramifiedOutside K Ω T where
  toFun := gsResFun T
  map_one' := by
    apply AlgEquiv.ext
    intro x
    apply Subtype.val_injective
    rw [gsResFun_apply h, AlgEquiv.one_apply, AlgEquiv.one_apply]
  map_mul' σ τ := by
    apply AlgEquiv.ext
    intro x
    apply Subtype.val_injective
    have e : (⟨((gsResFun T τ x : maxUnramifiedOutside K Ω T) : Ω),
        maxUnramifiedOutside_mono h (gsResFun T τ x).2⟩ : maxUnramifiedOutside K Ω S) =
        τ ⟨x, maxUnramifiedOutside_mono h x.2⟩ :=
      Subtype.val_injective (gsResFun_apply h τ x)
    rw [AlgEquiv.mul_apply (gsResFun T σ), gsResFun_apply h (σ * τ) x,
      gsResFun_apply h σ (gsResFun T τ x), e, AlgEquiv.mul_apply]

theorem gsRes_apply (h : T ⊆ S) (σ : galUnramifiedOutside K Ω S) (x : maxUnramifiedOutside K Ω T) :
    ((gsRes h σ x : maxUnramifiedOutside K Ω T) : Ω) =
      ((σ ⟨x, maxUnramifiedOutside_mono h x.2⟩ : maxUnramifiedOutside K Ω S) : Ω) :=
  gsResFun_apply h σ x

theorem gsRes_restrictNormalHom (h : T ⊆ S) (σ : Gal(Ω/K)) :
    gsRes h (AlgEquiv.restrictNormalHom (maxUnramifiedOutside K Ω S) σ) =
      AlgEquiv.restrictNormalHom (maxUnramifiedOutside K Ω T) σ := by
  apply AlgEquiv.ext
  intro x
  apply Subtype.val_injective
  rw [gsRes_apply, AlgEquiv.restrictNormalHom_apply, AlgEquiv.restrictNormalHom_apply]

theorem gsRes_surjective (h : T ⊆ S) : Function.Surjective (gsRes (Ω := Ω) h) := fun τ =>
  ⟨AlgEquiv.restrictNormalHom (maxUnramifiedOutside K Ω S) (gsAutExtend T τ), by
    rw [gsRes_restrictNormalHom]
    exact (AlgEquiv.restrictNormalHom_surjective (K₁ := maxUnramifiedOutside K Ω T) Ω τ).choose_spec⟩

theorem gsRes_gsRes (hTS : T ⊆ S) (hUT : U ⊆ T) (σ : galUnramifiedOutside K Ω S) :
    gsRes hUT (gsRes hTS σ) = gsRes (hUT.trans hTS) σ := by
  apply AlgEquiv.ext
  intro x
  apply Subtype.val_injective
  rw [gsRes_apply hUT, gsRes_apply hTS, gsRes_apply]

theorem mem_ker_gsRes (h : T ⊆ S) (σ : galUnramifiedOutside K Ω S) :
    σ ∈ (gsRes (Ω := Ω) h).ker ↔
      ∀ x : maxUnramifiedOutside K Ω T, σ ⟨x, maxUnramifiedOutside_mono h x.2⟩ =
        ⟨x, maxUnramifiedOutside_mono h x.2⟩ := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro hσ x
    apply Subtype.val_injective
    have := gsRes_apply h σ x
    rw [hσ] at this
    exact this.symm
  · intro hσ
    apply AlgEquiv.ext
    intro x
    apply Subtype.val_injective
    rw [gsRes_apply, hσ x, AlgEquiv.one_apply]

theorem continuous_gsRes (h : T ⊆ S) : Continuous (gsRes (Ω := Ω) h) := by
  have hq : Topology.IsQuotientMap
      (AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) (maxUnramifiedOutside K Ω S)) :=
    (InfiniteGalois.restrictNormalHom_continuous _).isClosedMap.isQuotientMap
      (InfiniteGalois.restrictNormalHom_continuous _) (AlgEquiv.restrictNormalHom_surjective Ω)
  rw [hq.continuous_iff]
  have e : ⇑(gsRes h) ∘ ⇑(AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) (maxUnramifiedOutside K Ω S)) =
      ⇑(AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) (maxUnramifiedOutside K Ω T)) :=
    funext (gsRes_restrictNormalHom h)
  rw [e]
  exact InfiniteGalois.restrictNormalHom_continuous _

def gsResCont (h : T ⊆ S) : galUnramifiedOutside K Ω S →ₜ* galUnramifiedOutside K Ω T :=
  ⟨gsRes h, continuous_gsRes h⟩

@[simp]
theorem gsResCont_apply (h : T ⊆ S) (σ : galUnramifiedOutside K Ω S) : gsResCont h σ = gsRes h σ :=
  rfl

section Local

variable {Kv Ωv : Type u} [Field Kv] [Field Ωv] [Algebra K Kv] [Algebra Kv Ωv] [Algebra K Ωv]
  [IsScalarTower K Kv Ωv]

end Local

end

end GroundTheory.ProfCoh
