import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowMinor
import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatDetHMapInjectiveIsometryStatement

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LoopC

section

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

omit [NumberField K] [StarRing K] in

theorem primInv_span_gmap (γ : V ≃ₗ[K] V) (M : Submodule (𝓞 K) V) :
    Submodule.span K ((Formalism.HermitianLatticesTheory.gmap γ M : Submodule (𝓞 K) V) : Set V) =
      (Submodule.span K (M : Set V)).map (γ : V →ₗ[K] V) := by
  unfold Formalism.HermitianLatticesTheory.gmap
  rw [Submodule.map_coe, ← Submodule.span_image]
  try rfl

omit [NumberField K] [StarRing K] in

theorem primInv_gmap_injective (γ : V ≃ₗ[K] V) :
    Function.Injective (fun M : Submodule (𝓞 K) V => Formalism.HermitianLatticesTheory.gmap γ M) := by
  intro M N hMN
  exact Submodule.map_injective_of_injective (f := (γ : V →ₗ[K] V).restrictScalars (𝓞 K))
    γ.injective hMN

omit [NumberField K] [StarRing K] in
theorem primInv_gmap_symm (γ : V ≃ₗ[K] V) (M : Submodule (𝓞 K) V) :
    Formalism.HermitianLatticesTheory.gmap γ⁻¹ (Formalism.HermitianLatticesTheory.gmap γ M) = M := by
  ext x
  unfold Formalism.HermitianLatticesTheory.gmap
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    change γ.symm (γ z) ∈ M
    rwa [γ.symm_apply_apply]
  · intro hx
    exact ⟨γ x, ⟨x, hx, rfl⟩, γ.symm_apply_apply x⟩

theorem primInv_mem (h : V →ₗ⋆[K] V →ₗ[K] K) (γ : V ≃ₗ[K] V) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom h)
    (L : Submodule (𝓞 K) V) (j de : ℕ) (M : Submodule (𝓞 K) V) (hM : M ∈ PrimSubs h L j de) :
    Formalism.HermitianLatticesTheory.gmap γ M ∈ PrimSubs h (Formalism.HermitianLatticesTheory.gmap γ L) j de := by
  obtain ⟨⟨hle, heq⟩, hrk, hdet⟩ := hM
  have hspan := primInv_span_gmap γ M
  refine ⟨⟨Submodule.map_mono hle, ?_⟩, ?_, ?_⟩
  ·
    have hres : ((Submodule.span K (M : Set V)).map (γ : V →ₗ[K] V)).restrictScalars (𝓞 K) =
        ((Submodule.span K (M : Set V)).restrictScalars (𝓞 K)).map
          ((γ : V →ₗ[K] V).restrictScalars (𝓞 K)) := by
      ext x; exact Iff.rfl
    rw [hspan, hres]
    unfold Formalism.HermitianLatticesTheory.gmap
    rw [← Submodule.map_inf ((γ : V →ₗ[K] V).restrictScalars (𝓞 K)) γ.injective, ← heq]
  · rw [hspan, LinearEquiv.finrank_map_eq]
    exact hrk
  · rw [← hdet]
    exact GlobalTheory.T.latDetH_map_injective_isometry K V V h h (γ : V →ₗ[K] V) γ.injective (fun x y => hγ x y) M

theorem primInv_le (h : V →ₗ⋆[K] V →ₗ[K] K) (γ : V ≃ₗ[K] V) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom h)
    (L : Submodule (𝓞 K) V) (j de : ℕ) : cntPrim h L j de ≤ cntPrim h (Formalism.HermitianLatticesTheory.gmap γ L) j de := by
  unfold cntPrim
  rw [← Set.InjOn.encard_image (f := fun M : Submodule (𝓞 K) V => Formalism.HermitianLatticesTheory.gmap γ M)
    (s := PrimSubs h L j de) (fun _ _ _ _ hab => primInv_gmap_injective γ hab)]
  have hsub : (fun M : Submodule (𝓞 K) V => Formalism.HermitianLatticesTheory.gmap γ M) '' PrimSubs h L j de ⊆
      PrimSubs h (Formalism.HermitianLatticesTheory.gmap γ L) j de := by
    rintro _ ⟨M, hM, rfl⟩
    exact primInv_mem h γ hγ L j de M hM
  first
    | exact Set.encard_le_encard hsub
    | exact Set.encard_mono hsub
    | exact Set.encard_le_card hsub

end

theorem cntPrim_gmap_isom : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), ∀ γ ∈ Formalism.HermitianLatticesTheory.isom h, ∀ (L : Submodule (𝓞 K) V) (j de : ℕ), cntPrim h (Formalism.HermitianLatticesTheory.gmap γ L) j de = cntPrim h L j de := by
  intro K V _ _ _ _ _ _ _ h γ hγ L j de
  refine le_antisymm ?_ (primInv_le h γ hγ L j de)
  have := primInv_le h γ⁻¹ (inv_mem hγ) (Formalism.HermitianLatticesTheory.gmap γ L) j de
  rwa [primInv_gmap_symm] at this

end GlobalTheory.LoopC
