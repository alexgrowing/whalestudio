import Mathlib
import GroundTheory.GlobalFields.IdeleGroups.SIdeleGroups.Places
import GroundTheory.GlobalFields.SemilocalAlgebras.Infinite

namespace GroundTheory.Global

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum AdeleBaseChange SemiLocal
open scoped NumberField.AdeleRing

noncomputable section

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

namespace IdeleGroup

section Infinite

variable (v : InfinitePlace K)

open Classical in

def infiniteAdeleAboveFun (a : (w : v.placesOver L) → w.1.Completion) (w : InfinitePlace L) :
    w.Completion :=
  if h : w ∈ v.placesOver L then a ⟨w, h⟩ else 1

omit [NumberField K] [NumberField L] in
theorem infiniteAdeleAboveFun_apply (a : (w : v.placesOver L) → w.1.Completion)
    (w : v.placesOver L) : infiniteAdeleAboveFun v a w.1 = a w := by
  rw [infiniteAdeleAboveFun, dif_pos w.2]

omit [NumberField K] [NumberField L] in
theorem infiniteAdeleAboveFun_apply_of_not (a : (w : v.placesOver L) → w.1.Completion)
    {w : InfinitePlace L} (h : w ∉ v.placesOver L) : infiniteAdeleAboveFun v a w = 1 := by
  rw [infiniteAdeleAboveFun, dif_neg h]

omit [NumberField K] [NumberField L] in
theorem infiniteAdeleAboveFun_one :
    infiniteAdeleAboveFun v (1 : (w : v.placesOver L) → w.1.Completion) = 1 := by
  funext w
  by_cases h : w ∈ v.placesOver L
  · exact infiniteAdeleAboveFun_apply v 1 ⟨w, h⟩
  · exact infiniteAdeleAboveFun_apply_of_not v 1 h

omit [NumberField K] [NumberField L] in
theorem infiniteAdeleAboveFun_mul (a b : (w : v.placesOver L) → w.1.Completion) :
    infiniteAdeleAboveFun v (a * b) = infiniteAdeleAboveFun v a * infiniteAdeleAboveFun v b := by
  funext w
  rw [Pi.mul_apply]
  by_cases h : w ∈ v.placesOver L
  · rw [infiniteAdeleAboveFun_apply v _ ⟨w, h⟩, infiniteAdeleAboveFun_apply v _ ⟨w, h⟩,
      infiniteAdeleAboveFun_apply v _ ⟨w, h⟩, Pi.mul_apply]
  · rw [infiniteAdeleAboveFun_apply_of_not v _ h, infiniteAdeleAboveFun_apply_of_not v _ h,
      infiniteAdeleAboveFun_apply_of_not v _ h, mul_one]

def infiniteAdeleAbove : ((w : v.placesOver L) → w.1.Completion) →* InfiniteAdeleRing L where
  toFun a := infiniteAdeleAboveFun v a
  map_one' := infiniteAdeleAboveFun_one v
  map_mul' a b := infiniteAdeleAboveFun_mul v a b

def infiniteEmbedAbove : ((w : v.placesOver L) → (w.1.Completion)ˣ) →* IdeleGroup L :=
  (Units.map (MonoidHom.prod (infiniteAdeleAbove v) 1 :
      ((w : v.placesOver L) → w.1.Completion) →*
        InfiniteAdeleRing L × FiniteAdeleRing (𝓞 L) L)).comp
    (MulEquiv.piUnits (M := fun w : v.placesOver L ↦ w.1.Completion)).symm.toMonoidHom

omit [NumberField K] in
theorem coe_infiniteEmbedAbove_snd (y : (w : v.placesOver L) → (w.1.Completion)ˣ) :
    ((infiniteEmbedAbove v y : IdeleGroup L) : 𝔸[L]).2 = 1 :=
  rfl

omit [NumberField K] in
theorem coe_infiniteEmbedAbove_fst (y : (w : v.placesOver L) → (w.1.Completion)ˣ)
    (w : v.placesOver L) : ((infiniteEmbedAbove v y : IdeleGroup L) : 𝔸[L]).1 w.1 = y w :=
  infiniteAdeleAboveFun_apply v _ w

omit [NumberField K] in
theorem coe_infiniteEmbedAbove_fst_of_not (y : (w : v.placesOver L) → (w.1.Completion)ˣ)
    {w : InfinitePlace L} (h : w ∉ v.placesOver L) :
    ((infiniteEmbedAbove v y : IdeleGroup L) : 𝔸[L]).1 w = 1 :=
  infiniteAdeleAboveFun_apply_of_not v _ h

def infiniteProjAbove : IdeleGroup L →* ((w : v.placesOver L) → (w.1.Completion)ˣ) :=
  MonoidHom.pi fun w ↦ infiniteProj w.1

omit [NumberField K] in
@[simp]
theorem coe_infiniteProjAbove_apply (x : IdeleGroup L) (w : v.placesOver L) :
    ((infiniteProjAbove v x w : (w.1.Completion)ˣ) : w.1.Completion) = (x : 𝔸[L]).1 w.1 :=
  rfl

omit [NumberField K] in
theorem infiniteProjAbove_infiniteEmbedAbove (y : (w : v.placesOver L) → (w.1.Completion)ˣ) :
    infiniteProjAbove v (infiniteEmbedAbove v y) = y :=
  funext fun w ↦ Units.ext (coe_infiniteEmbedAbove_fst v y w)

omit [NumberField K] [NumberField L] in

theorem comap_mem_placesOver (σ : L ≃ₐ[K] L) (w : v.placesOver L) :
    w.1.comap ((σ : L ≃+* L) : L →+* L) ∈ v.placesOver L := by
  rw [comap_eq_inv_smul]
  exact (σ⁻¹ • w).2

omit [NumberField K] [NumberField L] in
theorem mem_placesOver_of_smul_mem (σ : L ≃ₐ[K] L) {w : InfinitePlace L}
    (h : σ • w ∈ v.placesOver L) : w ∈ v.placesOver L := by
  have := (σ⁻¹ • (⟨σ • w, h⟩ : v.placesOver L)).2
  rwa [InfinitePlace.coe_smul_placesOver, inv_smul_smul] at this

omit [NumberField K] in

theorem infiniteProjAbove_smul_congr (σ : L ≃ₐ[K] L) {x y : IdeleGroup L}
    (h : infiniteProjAbove v x = infiniteProjAbove v y) :
    infiniteProjAbove v (σ • x) = infiniteProjAbove v (σ • y) := by
  funext u
  refine Units.ext ?_
  rw [coe_infiniteProjAbove_apply, coe_infiniteProjAbove_apply, coe_smul_idele, coe_smul_idele,
    smul_fst, smul_fst]
  congr 1
  exact congrArg (fun f : (w : v.placesOver L) → (w.1.Completion)ˣ ↦
    ((f ⟨u.1.comap ((σ : L ≃+* L) : L →+* L), comap_mem_placesOver v σ u⟩ : _) :
      (u.1.comap ((σ : L ≃+* L) : L →+* L)).Completion)) h

instance infiniteUnitsAboveAction :
    MulDistribMulAction (L ≃ₐ[K] L) ((w : v.placesOver L) → (w.1.Completion)ˣ) where
  smul σ y := infiniteProjAbove v (σ • infiniteEmbedAbove v y)
  one_smul y := by
    change infiniteProjAbove v ((1 : L ≃ₐ[K] L) • infiniteEmbedAbove v y) = y
    rw [one_smul, infiniteProjAbove_infiniteEmbedAbove]
  mul_smul σ τ y := by
    change infiniteProjAbove v ((σ * τ) • infiniteEmbedAbove v y) =
      infiniteProjAbove v
        (σ • infiniteEmbedAbove v (infiniteProjAbove v (τ • infiniteEmbedAbove v y)))
    rw [mul_smul]
    exact infiniteProjAbove_smul_congr v σ (infiniteProjAbove_infiniteEmbedAbove v _).symm
  smul_mul σ y z := by
    change infiniteProjAbove v (σ • infiniteEmbedAbove v (y * z)) =
      infiniteProjAbove v (σ • infiniteEmbedAbove v y) *
        infiniteProjAbove v (σ • infiniteEmbedAbove v z)
    rw [map_mul, smul_mul', map_mul]
  smul_one σ := by
    change infiniteProjAbove v (σ • infiniteEmbedAbove v 1) = 1
    rw [map_one, smul_one, map_one]

theorem infiniteUnitsAbove_smul_def (σ : L ≃ₐ[K] L)
    (y : (w : v.placesOver L) → (w.1.Completion)ˣ) :
    σ • y = infiniteProjAbove v (σ • infiniteEmbedAbove v y) :=
  rfl

theorem infiniteProjAbove_smul (σ : L ≃ₐ[K] L) (x : IdeleGroup L) :
    infiniteProjAbove v (σ • x) = σ • infiniteProjAbove v x :=
  infiniteProjAbove_smul_congr v σ (infiniteProjAbove_infiniteEmbedAbove v _).symm

theorem infiniteEmbedAbove_smul (σ : L ≃ₐ[K] L) (y : (w : v.placesOver L) → (w.1.Completion)ˣ) :
    infiniteEmbedAbove v (σ • y) = σ • infiniteEmbedAbove v y := by
  refine Units.ext (adele_ext ?_ fun u ↦ ?_)
  · funext u
    by_cases h : u ∈ v.placesOver L
    · rw [coe_infiniteEmbedAbove_fst v _ ⟨u, h⟩, infiniteUnitsAbove_smul_def,
        coe_infiniteProjAbove_apply]
    · rw [coe_infiniteEmbedAbove_fst_of_not v _ h, coe_smul_idele, smul_fst,
        coe_infiniteEmbedAbove_fst_of_not v _ ?_, map_one]
      rw [comap_eq_inv_smul]
      intro h'
      exact h (mem_placesOver_of_smul_mem v σ⁻¹ h')
  · rw [coe_infiniteEmbedAbove_snd, coe_smul_idele, smul_snd, coe_infiniteEmbedAbove_snd]
    exact (map_one (finiteCompletionMap _ u)).symm

omit [NumberField K] in

theorem infiniteProjAbove_infiniteEmbedAbove_of_ne {v v' : InfinitePlace K} (h : v' ≠ v)
    (y : (w : v.placesOver L) → (w.1.Completion)ˣ) :
    infiniteProjAbove v' (infiniteEmbedAbove v y) = 1 := by
  funext u
  refine Units.ext ?_
  rw [coe_infiniteProjAbove_apply, coe_infiniteEmbedAbove_fst_of_not v y]
  · rfl
  · intro hu
    apply h
    rw [← (InfinitePlace.liesOver_iff_comap_eq v' u.1).1 u.2,
      (InfinitePlace.liesOver_iff_comap_eq v u.1).1 hu]

omit [NumberField K] in

theorem finiteProjAbove_infiniteEmbedAbove (v' : HeightOneSpectrum (𝓞 K))
    (y : (w : v.placesOver L) → (w.1.Completion)ˣ) :
    finiteProjAbove v' (infiniteEmbedAbove v y) = 1 :=
  funext fun _ ↦ Units.ext rfl

theorem infiniteProjAbove_finiteEmbedAbove (v' : HeightOneSpectrum (𝓞 K))
    (y : (w : PlacesOver L v') → (w.1.adicCompletion L)ˣ) :
    infiniteProjAbove v (finiteEmbedAbove v' y) = 1 :=
  funext fun _ ↦ Units.ext rfl

theorem infiniteUnitsAbove_smul_apply (σ : L ≃ₐ[K] L)
    (y : (w : v.placesOver L) → (w.1.Completion)ˣ) (w : v.placesOver L) :
    (((σ • y) w : (w.1.Completion)ˣ) : w.1.Completion) =
      infiniteCompletionMap (σ : L ≃+* L) w.1
        (y ⟨w.1.comap ((σ : L ≃+* L) : L →+* L), comap_mem_placesOver v σ w⟩) := by
  rw [infiniteUnitsAbove_smul_def, coe_infiniteProjAbove_apply, coe_smul_idele, smul_fst,
    coe_infiniteEmbedAbove_fst v y ⟨_, comap_mem_placesOver v σ w⟩]

end Infinite

end IdeleGroup

end

end GroundTheory.Global
