import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MapMulVecMemOfMemSpan
open Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.SplitField

namespace GlobalTheory.SplitField

def coordMap {L E : Type} [Field L] [Field E] (f : L →+* E) (a : ℕ) :
    (Fin a → L) →ₛₗ[f] (Fin a → E) where
  toFun v := f ∘ v
  map_add' v w := by funext i; simp
  map_smul' c v := by funext i; simp [smul_eq_mul]

theorem coordMap_injective {L E : Type} [Field L] [Field E] (f : L →+* E) (a : ℕ) :
    Function.Injective (coordMap f a) := by
  intro v w h
  funext i
  exact f.injective (congrFun h i)

theorem descend_decomp {Γ L E : Type} [Group Γ] [Field L] [Field E] (f : L →+* E) {a n : ℕ}
    (τ : Γ →* GL (Fin a) L) (Vs : Fin n → Submodule E (Fin a → E)) (hint : DirectSum.IsInternal Vs)
    (hinv : ∀ m, IsInv (mapRep f τ) (Vs m))
    (hspan : ∀ m, Vs m ≤ Submodule.span E ((fun v => f ∘ v) '' {v : Fin a → L | f ∘ v ∈ Vs m})) :
    ∃ Us : Fin n → Submodule L (Fin a → L), DirectSum.IsInternal Us ∧
      ∀ m, IsInv τ (Us m) ∧ Submodule.span E ((fun v => f ∘ v) '' (Us m : Set (Fin a → L))) = Vs m := by
  classical
  set F := coordMap f a with hF
  let Us : Fin n → Submodule L (Fin a → L) := fun m => (Vs m).comap F
  have hUs : ∀ m, (Us m : Set (Fin a → L)) = {v : Fin a → L | f ∘ v ∈ Vs m} := fun m => rfl
  obtain ⟨hindV, htopV⟩ := (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top Vs).1 hint
  refine ⟨Us, ?_, fun m => ⟨?_, ?_⟩⟩
  · rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
    refine ⟨?_, ?_⟩
    · rw [iSupIndep_def]
      intro i
      rw [Submodule.disjoint_def]
      intro v hv1 hv2
      have hle : (⨆ (j : Fin n) (_ : j ≠ i), Us j) ≤ (⨆ (j : Fin n) (_ : j ≠ i), Vs j).comap F :=
        iSup₂_le fun j hj => Submodule.comap_mono (le_iSup₂ (f := fun j (_ : j ≠ i) => Vs j) j hj)
      have h1 : F v ∈ Vs i := hv1
      have h2 : F v ∈ ⨆ (j : Fin n) (_ : j ≠ i), Vs j := hle hv2
      have h3 := (Submodule.disjoint_def.1 ((iSupIndep_def.1 hindV) i)) _ h1 h2
      exact coordMap_injective f a (by rw [h3, map_zero])
    · rw [eq_top_iff]
      intro v _
      have hle : (⨆ m, Vs m) ≤ Submodule.span E ((fun v => f ∘ v) '' ((⨆ m, Us m : Submodule L (Fin a → L)) : Set (Fin a → L))) := by
        refine iSup_le fun m => (hspan m).trans (Submodule.span_mono (Set.image_mono ?_))
        rw [← hUs m]
        exact le_iSup Us m
      have hv : f ∘ v ∈ ⨆ m, Vs m := by rw [htopV]; exact Submodule.mem_top
      have := mem_span_of_map_mem_span f _ v (hle hv)
      rwa [Submodule.span_eq] at this
  · intro g v hv
    have hv' : f ∘ v ∈ Vs m := hv
    show f ∘ ((τ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L).mulVec v ∈ Vs m
    have hm : f ∘ ((τ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L).mulVec v =
        ((mapRep f τ g : GL (Fin a) E) : Matrix (Fin a) (Fin a) E).mulVec (f ∘ v) := by
      funext i
      exact RingHom.map_mulVec f _ v i
    rw [hm]
    exact hinv m g _ hv'
  · refine le_antisymm ?_ ?_
    · rw [Submodule.span_le]
      rintro _ ⟨v, hv, rfl⟩
      exact hv
    · rw [hUs m]
      exact hspan m

end GlobalTheory.SplitField
