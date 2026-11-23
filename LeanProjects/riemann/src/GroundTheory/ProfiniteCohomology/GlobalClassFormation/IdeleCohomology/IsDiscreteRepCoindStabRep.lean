import Mathlib
import GroundTheory.ProfiniteCohomology.Shapiro
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleCohomology.Product
import GroundTheory.GlobalFields.HerbrandQuotients.CycTateNegOneOrbitEquivSymmMk
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits GroundTheory.Global

universe u

section Product

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [DiscreteTopology G]
  {ι : Type*} {P : Rep.{u} k G} {A : ι → Rep.{u} k G}

theorem cohomology_pi_bijective (p : ∀ i, P ⟶ A i)
    (hp : Function.Bijective fun (x : P) (i : ι) => (p i).hom x) (n : ℕ) :
    Function.Bijective fun (x : cohomology P n) (i : ι) =>
      (cohomologyMapAlong (MonoidHom.id G) continuous_id (p i) n).hom x := by
  refine homologyMap_pi_bijective (fun i => cochainsMapAlong (MonoidHom.id G) continuous_id (p i))
    (fun m => ⟨fun f f' h => ?_, fun F => ?_⟩) n
  · apply Subtype.ext
    funext g
    apply hp.1
    funext i
    exact congrFun (congrArg Subtype.val (congrFun h i)) g
  · refine ⟨⟨fun g => Function.surjInv hp.2 (fun i => (F i).1 g), IsLocallyConstant.of_discrete _⟩,
      funext fun i => Subtype.ext (funext fun g => ?_)⟩
    exact congrFun (Function.surjInv_eq hp.2 (fun i => (F i).1 g)) i

noncomputable def cohomologyPiEquiv (p : ∀ i, P ⟶ A i)
    (hp : Function.Bijective fun (x : P) (i : ι) => (p i).hom x) (n : ℕ) :
    cohomology P n ≃ₗ[k] ∀ i, cohomology (A i) n :=
  LinearEquiv.ofBijective
    (LinearMap.pi fun i => (cohomologyMapAlong (MonoidHom.id G) continuous_id (p i) n).hom)
    (cohomology_pi_bijective p hp n)

@[simp]
theorem cohomologyPiEquiv_apply (p : ∀ i, P ⟶ A i)
    (hp : Function.Bijective fun (x : P) (i : ι) => (p i).hom x) (n : ℕ)
    (x : cohomology P n) (i : ι) :
    cohomologyPiEquiv p hp n x i =
      (cohomologyMapAlong (MonoidHom.id G) continuous_id (p i) n).hom x :=
  rfl

end Product

section Stabilizer

variable {k G X : Type u} [CommRing k] [Group G] [MulAction G X]
  {M : X → Type u} [∀ x, AddCommGroup (M x)] [∀ x, Module k (M x)]
  {ρ : Representation k G (∀ x, M x)} (hρ : PermutesFactors ρ) {x₀ : X} {D : Subgroup G}
  (hD : ∀ g, g ∈ D ↔ g • x₀ = x₀)

include hρ in

theorem _root_.GroundTheory.Global.PermutesFactors.apply_base_eq {g : G} (hg : g • x₀ = x₀) {f f' : ∀ x, M x}
    (h : f x₀ = f' x₀) : ρ g f x₀ = ρ g f' x₀ := by
  have := hρ.apply_eq g h
  rwa [hg] at this

variable (ρ x₀ D) in
include hρ hD in
open Classical in

noncomputable def stabRep : Representation k D (M x₀) where
  toFun d := (LinearMap.proj x₀).comp ((ρ d).comp (LinearMap.single k M x₀))
  map_one' := by
    ext a
    simp
  map_mul' d d' := by
    ext a
    simp only [Subgroup.coe_mul, map_mul, LinearMap.coe_comp, LinearMap.coe_proj,
      Function.comp_apply, Function.eval, LinearMap.coe_single, Module.End.mul_apply]
    exact hρ.apply_base_eq ((hD d).1 d.2) (Pi.single_eq_same x₀ _).symm

open Classical in
theorem stabRep_apply (d : D) (a : M x₀) :
    stabRep ρ hρ x₀ D hD d a = ρ d (Pi.single x₀ a) x₀ :=
  rfl

theorem apply_base_eq_stabRep (d : D) (f : ∀ x, M x) :
    ρ d f x₀ = stabRep ρ hρ x₀ D hD d (f x₀) := by
  classical
  rw [stabRep_apply]
  exact hρ.apply_base_eq ((hD d).1 d.2) (Pi.single_eq_same x₀ _).symm

noncomputable def orbitProj :
    Rep.res D.subtype (Rep.of ρ) ⟶ Rep.of (stabRep ρ hρ x₀ D hD) :=
  Rep.ofHom ⟨LinearMap.proj x₀, fun d => LinearMap.ext fun f =>
    apply_base_eq_stabRep hρ hD d f⟩

@[simp]
theorem orbitProj_hom_apply (f : ∀ x, M x) : (orbitProj hρ hD).hom f = f x₀ :=
  rfl

noncomputable def toCoindLinear :
    (∀ x, M x) →ₗ[k] Representation.coindV D.subtype (stabRep ρ hρ x₀ D hD) where
  toFun f := ⟨fun h => ρ h f x₀, fun d h => by
    change ρ (d * h) f x₀ = stabRep ρ hρ x₀ D hD d (ρ h f x₀)
    rw [map_mul, Module.End.mul_apply, apply_base_eq_stabRep hρ hD]⟩
  map_add' f f' := by
    apply Subtype.ext
    funext h
    simp only [map_add, Pi.add_apply, Submodule.coe_add]
  map_smul' c f := by
    apply Subtype.ext
    funext h
    simp only [map_smul, Pi.smul_apply, RingHom.id_apply, Submodule.coe_smul]

@[simp]
theorem toCoindLinear_apply (f : ∀ x, M x) (h : G) :
    (toCoindLinear hρ hD f).1 h = ρ h f x₀ :=
  rfl

variable [MulAction.IsPretransitive G X]

theorem toCoindLinear_bijective : Function.Bijective (toCoindLinear hρ hD) := by
  constructor
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro f hf
    funext y
    obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G x₀ y
    have h0 : ρ g⁻¹ f x₀ = 0 := congrFun (congrArg Subtype.val hf) g⁻¹
    have := hρ g (ρ g⁻¹ f) x₀ h0
    rwa [Representation.self_inv_apply] at this
  · intro F
    classical
    let r : X → G := fun y => (MulAction.exists_smul_eq G x₀ y).choose
    refine ⟨fun y => ρ (r y) (Pi.single x₀ (F.1 (r y)⁻¹)) y, Subtype.ext (funext fun h => ?_)⟩
    change ρ h (fun y => ρ (r y) (Pi.single x₀ (F.1 (r y)⁻¹)) y) x₀ = F.1 h
    set y := h⁻¹ • x₀ with hy
    have hry : r y • x₀ = y := (MulAction.exists_smul_eq G x₀ y).choose_spec
    have hhy : h • y = x₀ := by rw [hy, smul_inv_smul]
    have key : ∀ {z : X} (hz : h • y = z) {f f' : ∀ x, M x}, f y = f' y → ρ h f z = ρ h f' z := by
      intro z hz f f' hff'
      subst hz
      exact hρ.apply_eq h hff'
    refine (key hhy (f := fun z => ρ (r z) (Pi.single x₀ (F.1 (r z)⁻¹)) z)
      (f' := ρ (r y) (Pi.single x₀ (F.1 (r y)⁻¹))) rfl).trans ?_
    rw [← Module.End.mul_apply, ← map_mul]
    have hd : h * r y ∈ D := (hD _).2 (by rw [mul_smul, hry, hhy])
    have h1 := apply_base_eq_stabRep hρ hD ⟨h * r y, hd⟩ (Pi.single x₀ (F.1 (r y)⁻¹))
    simp only [Pi.single_eq_same] at h1
    rw [h1, ← F.2 ⟨h * r y, hd⟩ (r y)⁻¹]
    simp

noncomputable def orbitCoindIso :
    Rep.of ρ ≅ Rep.coind D.subtype (Rep.of (stabRep ρ hρ x₀ D hD)) :=
  Rep.mkIso (Representation.Equiv.mk
    (LinearEquiv.ofBijective (toCoindLinear hρ hD) (toCoindLinear_bijective hρ hD))
    fun g => LinearMap.ext fun f => Subtype.ext (funext fun h => by
      change ρ h (ρ g f) x₀ = ρ (h * g) f x₀
      rw [map_mul, Module.End.mul_apply]))

@[simp]
theorem orbitCoindIso_hom_apply (f : ∀ x, M x) (h : G) :
    ((orbitCoindIso hρ hD).hom.hom f).1 h = ρ h f x₀ :=
  rfl

end Stabilizer

section Shapiro

variable {k G X : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MulAction G X] [MulAction.IsPretransitive G X]
  {M : X → Type u} [∀ x, AddCommGroup (M x)] [∀ x, Module k (M x)]
  {ρ : Representation k G (∀ x, M x)} (hρ : PermutesFactors ρ) {x₀ : X} (U : OpenSubgroup G)
  (hU : ∀ g, g ∈ (U : Subgroup G) ↔ g • x₀ = x₀)
  [IsDiscreteRep (Rep.of ρ)] [IsDiscreteRep (Rep.of (stabRep ρ hρ x₀ (U : Subgroup G) hU))]

instance isDiscreteRep_coind_stabRep :
    IsDiscreteRep (Rep.coind (U : Subgroup G).subtype (Rep.of (stabRep ρ hρ x₀ (U : Subgroup G) hU))) :=
  isDiscreteRep_coind U _

theorem orbitProj_eq_shapiroMap (n : ℕ) :
    cohomologyMapAlong (U : Subgroup G).subtype (continuous_subgroup_subtype _)
      (orbitProj hρ hU) n =
      cohomologyMap (orbitCoindIso hρ hU).hom n ≫
        shapiroMap U (Rep.of (stabRep ρ hρ x₀ (U : Subgroup G) hU)) n := by
  have h : orbitProj hρ hU = (Rep.resFunctor (U : Subgroup G).subtype).map
      (orbitCoindIso hρ hU).hom ≫
      coindEvalOne (U : Subgroup G) (Rep.of (stabRep ρ hρ x₀ (U : Subgroup G) hU)) := by
    ext f
    change f x₀ = ρ 1 f x₀
    rw [map_one, Module.End.one_apply]
  rw [← cohomologyMapAlong_id_eq_cohomologyMap, shapiroMap_eq, ← cohomologyMapAlong_comp, ← h]
  rfl

instance isIso_orbitProj (n : ℕ) :
    IsIso (cohomologyMapAlong (U : Subgroup G).subtype (continuous_subgroup_subtype _)
      (orbitProj hρ hU) n) := by
  rw [orbitProj_eq_shapiroMap]
  have : IsIso (cohomologyMap (orbitCoindIso hρ hU).hom n) :=
    ⟨cohomologyMap (orbitCoindIso hρ hU).inv n, by
      rw [← cohomologyMap_comp, Iso.hom_inv_id, cohomologyMap_id], by
      rw [← cohomologyMap_comp, Iso.inv_hom_id, cohomologyMap_id]⟩
  infer_instance

noncomputable def orbitShapiroIso (n : ℕ) :
    cohomology (Rep.of ρ) n ≅ cohomology (Rep.of (stabRep ρ hρ x₀ (U : Subgroup G) hU)) n :=
  asIso (cohomologyMapAlong (U : Subgroup G).subtype (continuous_subgroup_subtype _)
    (orbitProj hρ hU) n)

@[simp]
theorem orbitShapiroIso_hom (n : ℕ) :
    (orbitShapiroIso hρ U hU n).hom =
      cohomologyMapAlong (U : Subgroup G).subtype (continuous_subgroup_subtype _)
        (orbitProj hρ hU) n :=
  rfl

end Shapiro

end GroundTheory.ProfCoh
