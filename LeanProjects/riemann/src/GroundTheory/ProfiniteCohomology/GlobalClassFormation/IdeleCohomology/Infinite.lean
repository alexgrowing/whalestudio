import Mathlib
import GroundTheory.GlobalFields.IdeleGroups.SIdeleGroups.InfinitePlaces
import GroundTheory.GlobalFields.IdeleGroups.LocalHerbrandInfinite
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleCohomology.Finite
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits NumberField GroundTheory.Global GroundTheory.Global.IdeleGroup
  GroundTheory.Global.AdeleBaseChange

open scoped NumberField.LiesOver

section Maps

variable {M : Type} [Field M]

noncomputable def completionCongr {u u' : InfinitePlace M} (h : u = u') :
    u.Completion ≃+* u'.Completion :=
  h ▸ RingEquiv.refl _

theorem continuous_completionCongr {u u' : InfinitePlace M} (h : u = u') :
    Continuous (completionCongr h) := by
  subst h
  exact continuous_id

theorem completionCongr_algebraMap {u u' : InfinitePlace M} (h : u = u') (x : M) :
    completionCongr h (algebraMap M u.Completion x) = algebraMap M u'.Completion x := by
  subst h
  rfl

theorem continuous_infiniteCompletionMap {M' : Type} [Field M'] [NumberField M] [NumberField M']
    (τ : M ≃+* M') (w' : InfinitePlace M') : Continuous (infiniteCompletionMap τ w') := by
  let _ : Algebra M M' := (τ : M →+* M').toAlgebra
  exact NumberField.LiesOver.continuous_completionMap

end Maps

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : InfinitePlace K)

section Representation

variable (L) in

noncomputable abbrev infiniteUnitsAboveRep :
    Representation ℤ Gal(L/K) (∀ w : v.placesOver L, Additive (w.1.Completion)ˣ) :=
  piUnitsRep

theorem infiniteUnitsAbove_smul_apply_of_eq (σ : Gal(L/K))
    (y : (w : v.placesOver L) → (w.1.Completion)ˣ) (u w : v.placesOver L)
    (h : u.1 = w.1.comap ((σ : L ≃+* L) : L →+* L)) :
    (((σ • y) w : (w.1.Completion)ˣ) : w.1.Completion) =
      infiniteCompletionMap (σ : L ≃+* L) w.1 (completionCongr h (y u)) := by
  obtain rfl : u = ⟨w.1.comap ((σ : L ≃+* L) : L →+* L), comap_mem_placesOver v σ w⟩ :=
    Subtype.ext h
  exact infiniteUnitsAbove_smul_apply v σ y w

omit [NumberField K] [NumberField L] in
theorem comap_smul_placesOver (σ : Gal(L/K)) (w : v.placesOver L) :
    w.1 = (σ • w).1.comap ((σ : L ≃+* L) : L →+* L) := by
  rw [comap_eq_inv_smul, InfinitePlace.coe_smul_placesOver, inv_smul_smul]

theorem permutesFactors_infiniteUnitsAboveRep : PermutesFactors (infiniteUnitsAboveRep L v) := by
  intro σ f w hf
  apply Additive.toMul.injective
  apply Units.ext
  change (((σ • fun x => (f x).toMul) (σ • w) : ((σ • w).1.Completion)ˣ) :
    (σ • w).1.Completion) = 1
  rw [infiniteUnitsAbove_smul_apply_of_eq v σ _ w (σ • w) (comap_smul_placesOver v σ w)]
  rw [hf]
  change infiniteCompletionMap _ _ (completionCongr _ 1) = 1
  rw [map_one, map_one]

noncomputable def infiniteProjAboveRep : ideleRep K L ⟶ Rep.of (infiniteUnitsAboveRep L v) :=
  Rep.ofHom ⟨AddMonoidHom.toIntLinearMap
    { toFun := fun x w => Additive.ofMul (infiniteProjAbove v x.toMul w)
      map_zero' := by
        funext w
        change Additive.ofMul (infiniteProjAbove v 1 w) = 0
        rw [map_one]
        rfl
      map_add' := fun x y => by
        funext w
        change Additive.ofMul (infiniteProjAbove v (x.toMul * y.toMul) w) = _
        rw [map_mul]
        rfl },
    fun σ => LinearMap.ext fun x => by
      funext w
      change Additive.ofMul (infiniteProjAbove v (σ • x.toMul) w) = _
      rw [infiniteProjAbove_smul]
      rfl⟩

@[simp]
theorem infiniteProjAboveRep_hom_apply (x : ideleRep K L) (w : v.placesOver L) :
    (infiniteProjAboveRep v).hom x w = Additive.ofMul (infiniteProjAbove v x.toMul w) :=
  rfl

noncomputable def infiniteEmbedAboveRep : Rep.of (infiniteUnitsAboveRep L v) ⟶ ideleRep K L :=
  Rep.ofHom ⟨AddMonoidHom.toIntLinearMap
    { toFun := fun y => Additive.ofMul (infiniteEmbedAbove v fun w => (y w).toMul)
      map_zero' := by
        change Additive.ofMul (infiniteEmbedAbove v 1) = 0
        rw [map_one]
        rfl
      map_add' := fun y z => by
        change Additive.ofMul
          (infiniteEmbedAbove v ((fun w => (y w).toMul) * fun w => (z w).toMul)) = _
        rw [map_mul]
        rfl },
    fun σ => LinearMap.ext fun y => by
      change Additive.ofMul (infiniteEmbedAbove v (σ • fun w => (y w).toMul)) = _
      rw [infiniteEmbedAbove_smul]
      rfl⟩

@[simp]
theorem infiniteEmbedAboveRep_hom_apply (y : ∀ w : v.placesOver L, Additive (w.1.Completion)ˣ) :
    (infiniteEmbedAboveRep v).hom y =
      Additive.ofMul (infiniteEmbedAbove v fun w => (y w).toMul) :=
  rfl

theorem infiniteEmbedAboveRep_comp_infiniteProjAboveRep :
    infiniteEmbedAboveRep (L := L) v ≫ infiniteProjAboveRep (L := L) v = 𝟙 _ := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro y
  funext w
  change Additive.ofMul (infiniteProjAbove v (infiniteEmbedAbove v fun w => (y w).toMul) w) = y w
  rw [infiniteProjAbove_infiniteEmbedAbove]
  rfl

theorem infiniteEmbedAboveRep_comp_infiniteProjAboveRep_of_ne {v v' : InfinitePlace K}
    (h : v' ≠ v) : infiniteEmbedAboveRep (L := L) v ≫ infiniteProjAboveRep (L := L) v' = 0 := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro y
  funext w
  change Additive.ofMul (infiniteProjAbove v' (infiniteEmbedAbove v fun w => (y w).toMul) w) = 0
  rw [infiniteProjAbove_infiniteEmbedAbove_of_ne h]
  rfl

theorem infiniteEmbedAboveRep_comp_finiteProjAboveRep (v' : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    infiniteEmbedAboveRep (L := L) v ≫ finiteProjAboveRep (L := L) v' = 0 := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro y
  funext w
  change Additive.ofMul (finiteProjAbove v' (infiniteEmbedAbove v fun w => (y w).toMul) w) = 0
  rw [finiteProjAbove_infiniteEmbedAbove]
  rfl

theorem finiteEmbedAboveRep_comp_infiniteProjAboveRep (v' : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    finiteEmbedAboveRep (L := L) v' ≫ infiniteProjAboveRep (L := L) v = 0 := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro y
  funext w
  change Additive.ofMul (infiniteProjAbove v (finiteEmbedAbove v' fun w => (y w).toMul) w) = 0
  rw [infiniteProjAbove_finiteEmbedAbove]
  rfl

end Representation

section Decomposition

variable (w : v.placesOver L)

omit [NumberField K] [NumberField L] in

theorem mem_stabilizer_iff_smul_eq_infinite (σ : Gal(L/K)) :
    σ ∈ MulAction.stabilizer Gal(L/K) w.1 ↔ σ • w = w := by
  rw [MulAction.mem_stabilizer_iff, Subtype.ext_iff, InfinitePlace.coe_smul_placesOver]

omit [NumberField K] in

theorem infiniteCompletionMap_eq_decomposition (σ : MulAction.stabilizer Gal(L/K) w.1)
    (h : w.1 = w.1.comap (((σ : Gal(L/K)) : L ≃+* L) : L →+* L)) (x : w.1.Completion) :
    infiniteCompletionMap ((σ : Gal(L/K)) : L ≃+* L) w.1 (completionCongr h x) = σ • x := by
  rw [infiniteDecomposition_smul_def]
  have := ringHom_ext_completion w.1
    (f := (infiniteCompletionMap ((σ : Gal(L/K)) : L ≃+* L) w.1).comp (completionCongr h).toRingHom)
    ((continuous_infiniteCompletionMap _ _).comp (continuous_completionCongr h))
    (continuous_completionRingHomOf σ.2) fun y => by
      rw [completionRingHomOf_coe]
      change infiniteCompletionMap _ w.1 (completionCongr h (algebraMap L w.1.Completion y.ofAbs)) =
        algebraMap L w.1.Completion (withAbsMapOf w.1 (σ : Gal(L/K)) y).ofAbs
      rw [completionCongr_algebraMap, infiniteCompletionMap_algebraMap, ofAbs_withAbsMapOf]
      rfl
  exact congrFun (congrArg DFunLike.coe this) x

theorem stabRep_infiniteUnitsAboveRep (σ : MulAction.stabilizer Gal(L/K) w.1)
    (a : Additive (w.1.Completion)ˣ) :
    stabRep (infiniteUnitsAboveRep L v) (permutesFactors_infiniteUnitsAboveRep v) w
        (MulAction.stabilizer Gal(L/K) w.1) (mem_stabilizer_iff_smul_eq_infinite v w) σ a =
      Representation.ofMulDistribMulAction (MulAction.stabilizer Gal(L/K) w.1)
        (w.1.Completion)ˣ σ a := by
  classical
  rw [stabRep_apply]
  apply Additive.toMul.injective
  apply Units.ext
  have hw : w = (σ : Gal(L/K)) • w := ((mem_stabilizer_iff_smul_eq_infinite v w σ).1 σ.2).symm
  have h : w.1 = w.1.comap (((σ : Gal(L/K)) : L ≃+* L) : L →+* L) := by
    have h' := comap_smul_placesOver v (σ : Gal(L/K)) w
    rwa [← hw] at h'
  simp only [piUnitsRep_apply, toMul_ofMul]
  rw [infiniteUnitsAbove_smul_apply_of_eq v (σ : Gal(L/K)) _ w w h,
    infiniteCompletionMap_eq_decomposition]
  simp only [Pi.single_eq_same]
  rfl

noncomputable def stabRepInfiniteIso :
    Rep.of (stabRep (infiniteUnitsAboveRep L v) (permutesFactors_infiniteUnitsAboveRep v) w
        (MulAction.stabilizer Gal(L/K) w.1) (mem_stabilizer_iff_smul_eq_infinite v w)) ≅
      Rep.ofMulDistribMulAction (MulAction.stabilizer Gal(L/K) w.1) (w.1.Completion)ˣ :=
  Rep.mkIso (Representation.Equiv.mk (LinearEquiv.refl ℤ _) fun σ =>
    LinearMap.ext fun a => stabRep_infiniteUnitsAboveRep v w σ a)

variable [IsGalois K L]

noncomputable def infiniteShapiroIso (n : ℕ) :
    cohomology (Rep.of (infiniteUnitsAboveRep L v)) n ≅
      cohomology (Rep.ofMulDistribMulAction (MulAction.stabilizer Gal(L/K) w.1)
        (w.1.Completion)ˣ) n :=
  orbitShapiroIso (permutesFactors_infiniteUnitsAboveRep v)
      ⟨MulAction.stabilizer Gal(L/K) w.1, isOpen_discrete _⟩
      (mem_stabilizer_iff_smul_eq_infinite v w) n ≪≫
    cohomologyIsoOfIso (stabRepInfiniteIso v w) n

end Decomposition

end GroundTheory.ProfCoh
