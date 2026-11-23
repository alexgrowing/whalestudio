import Mathlib
import GroundTheory.ProfiniteCohomology.CupProducts.Functoriality
import GroundTheory.ProfiniteCohomology.Shapiro
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory TensorProduct

universe u

variable {k G : Type u} [CommRing k] [Group G]

section Coind

variable (U : Subgroup G) (A B : Rep.{u} k G)

def coindTensorRightFun (f : Rep.coind U.subtype (Rep.res U.subtype A)) (b : B) :
    Rep.coind U.subtype (Rep.res U.subtype (A ⊗ B)) :=
  ⟨fun x => (f.1 x ⊗ₜ[k] B.ρ x b : (A ⊗ B : Rep k G)), fun u x => by
    change f.1 (U.subtype u * x) ⊗ₜ[k] B.ρ (U.subtype u * x) b =
      A.ρ (u : G) (f.1 x) ⊗ₜ[k] B.ρ (u : G) (B.ρ x b)
    rw [f.2 u x, map_mul, Module.End.mul_apply]
    rfl⟩

def coindTensorLeftFun (a : A) (f : Rep.coind U.subtype (Rep.res U.subtype B)) :
    Rep.coind U.subtype (Rep.res U.subtype (A ⊗ B)) :=
  ⟨fun x => (A.ρ x a ⊗ₜ[k] f.1 x : (A ⊗ B : Rep k G)), fun u x => by
    change A.ρ (U.subtype u * x) a ⊗ₜ[k] f.1 (U.subtype u * x) =
      A.ρ (u : G) (A.ρ x a) ⊗ₜ[k] B.ρ (u : G) (f.1 x)
    rw [f.2 u x, map_mul, Module.End.mul_apply]
    rfl⟩

def coindTensorRight :
    Rep.coind U.subtype (Rep.res U.subtype A) ⊗ B ⟶
      Rep.coind U.subtype (Rep.res U.subtype (A ⊗ B)) :=
  Rep.ofHom ⟨TensorProduct.lift (LinearMap.mk₂ k (coindTensorRightFun U A B)
      (fun f f' b => Subtype.ext (funext fun x => TensorProduct.add_tmul _ _ _))
      (fun c f b => Subtype.ext (funext fun x => (TensorProduct.smul_tmul' _ _ _).symm))
      (fun f b b' => Subtype.ext (funext fun x => by
        change f.1 x ⊗ₜ[k] B.ρ x (b + b') = f.1 x ⊗ₜ[k] B.ρ x b + f.1 x ⊗ₜ[k] B.ρ x b'
        rw [map_add, TensorProduct.tmul_add]))
      (fun c f b => Subtype.ext (funext fun x => by
        change f.1 x ⊗ₜ[k] B.ρ x (c • b) = c • (f.1 x ⊗ₜ[k] B.ρ x b)
        rw [map_smul, TensorProduct.tmul_smul]))),
    fun g => TensorProduct.ext' fun f b => Subtype.ext (funext fun x => by
      change f.1 (x * g) ⊗ₜ[k] B.ρ x (B.ρ g b) = f.1 (x * g) ⊗ₜ[k] B.ρ (x * g) b
      rw [map_mul, Module.End.mul_apply])⟩

def coindTensorLeft :
    A ⊗ Rep.coind U.subtype (Rep.res U.subtype B) ⟶
      Rep.coind U.subtype (Rep.res U.subtype (A ⊗ B)) :=
  Rep.ofHom ⟨TensorProduct.lift (LinearMap.mk₂ k (coindTensorLeftFun U A B)
      (fun a a' f => Subtype.ext (funext fun x => by
        change A.ρ x (a + a') ⊗ₜ[k] f.1 x = A.ρ x a ⊗ₜ[k] f.1 x + A.ρ x a' ⊗ₜ[k] f.1 x
        rw [map_add, TensorProduct.add_tmul]))
      (fun c a f => Subtype.ext (funext fun x => by
        change A.ρ x (c • a) ⊗ₜ[k] f.1 x = c • (A.ρ x a ⊗ₜ[k] f.1 x)
        rw [map_smul, TensorProduct.smul_tmul']))
      (fun a f f' => Subtype.ext (funext fun x => TensorProduct.tmul_add _ _ _))
      (fun c a f => Subtype.ext (funext fun x => TensorProduct.tmul_smul _ _ _))),
    fun g => TensorProduct.ext' fun a f => Subtype.ext (funext fun x => by
      change A.ρ x (A.ρ g a) ⊗ₜ[k] f.1 (x * g) = A.ρ (x * g) a ⊗ₜ[k] f.1 (x * g)
      rw [map_mul, Module.End.mul_apply])⟩

theorem coindTensorRight_comp_coindEvalOne :
    (Rep.resFunctor U.subtype).map (coindTensorRight U A B) ≫
        coindEvalOne U (Rep.res U.subtype (A ⊗ B)) =
      resTensorHom U.subtype (coindEvalOne U (Rep.res U.subtype A)) (𝟙 _) ≫
        (resTensorIso U.subtype A B).inv := by
  ext z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul f b =>
    change f.1 1 ⊗ₜ[k] B.ρ 1 b = f.1 1 ⊗ₜ[k] b
    rw [map_one, Module.End.one_apply]
  | add z z' hz hz' => rw [map_add, map_add, hz, hz']

variable [U.FiniteIndex]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

theorem coindTensorRight_comp_coindTrace :
    coindTensorRight U A B ≫ coindTrace U (A ⊗ B) = coindTrace U A ▷ B := by
  ext z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul f b =>
    change (coindTrace U (A ⊗ B)).hom ((coindTensorRight U A B).hom (f ⊗ₜ[k] b)) =
      (coindTrace U A).hom f ⊗ₜ[k] b
    rw [coindTrace_hom_apply, coindTrace_hom_apply, TensorProduct.sum_tmul]
    refine Finset.sum_congr rfl fun c _ => ?_
    change (A ⊗ B).ρ c.out (f.1 c.out⁻¹ ⊗ₜ[k] B.ρ c.out⁻¹ b) = A.ρ c.out (f.1 c.out⁻¹) ⊗ₜ[k] b
    rw [GroundTheory.GroupCoh.tensor_ρ_tmul, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      Module.End.one_apply]
  | add z z' hz hz' => rw [map_add, map_add, hz, hz']

end Coind

variable [TopologicalSpace G] [IsTopologicalGroup G]

section Composition

variable {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (φ : H →* G)
  (hφ : Continuous φ) {p : ℕ}

theorem cohomologyMapAlong_cohomologyMap {A A' : Rep.{u} k G} {B : Rep.{u} k H} [IsDiscreteRep A]
    [IsDiscreteRep A'] [IsDiscreteRep B] (f : A ⟶ A') (g : Rep.res φ A' ⟶ B)
    (w : cohomology A p) :
    cohomologyMapAlong φ hφ g p (cohomologyMap f p w) =
      cohomologyMapAlong φ hφ ((Rep.resFunctor φ).map f ≫ g) p w := by
  induction w using cohomology_induction_on with | h w => ?_
  rw [cohomologyMap_cohomologyπ, cohomologyMapAlong_cohomologyπ, cohomologyMapAlong_cohomologyπ]
  congr 1
  apply cocycles_ext
  rw [cochainOf_cocycleι_cocyclesMapAlong, cochainOf_cocycleι_cocyclesMapAlong,
    cochainOf_cocycleι_cyclesMap]
  rfl

theorem cohomologyMap_cohomologyMapAlong {A : Rep.{u} k G} {B B' : Rep.{u} k H} [IsDiscreteRep A]
    [IsDiscreteRep B] [IsDiscreteRep B'] (f : Rep.res φ A ⟶ B) (g : B ⟶ B')
    (w : cohomology A p) :
    cohomologyMap g p (cohomologyMapAlong φ hφ f p w) = cohomologyMapAlong φ hφ (f ≫ g) p w := by
  induction w using cohomology_induction_on with | h w => ?_
  rw [cohomologyMapAlong_cohomologyπ, cohomologyMap_cohomologyπ, cohomologyMapAlong_cohomologyπ]
  congr 1
  apply cocycles_ext
  rw [cochainOf_cocycleι_cyclesMap, cochainOf_cocycleι_cocyclesMapAlong,
    cochainOf_cocycleι_cocyclesMapAlong]
  rfl

end Composition

section Projection

variable [CompactSpace G] (U : OpenSubgroup G) {A B : Rep.{u} k G} [IsDiscreteRep A]
  [IsDiscreteRep B] {p q n : ℕ}

instance isDiscreteRep_coind_res_tensor_right :
    IsDiscreteRep (Rep.coind (U : Subgroup G).subtype (Rep.res (U : Subgroup G).subtype A) ⊗ B) :=
  isDiscreteRep_tensor _ _

theorem shapiroMap_inv_apply {C : Rep.{u} k (U : Subgroup G)} [IsDiscreteRep C] (m : ℕ)
    (w : cohomology C m) : shapiroMap U C m (inv (shapiroMap U C m) w) = w :=
  ConcreteCategory.congr_hom (IsIso.inv_hom_id (shapiroMap U C m)) w

theorem inv_shapiroMap_apply {C : Rep.{u} k (U : Subgroup G)} [IsDiscreteRep C] (m : ℕ)
    (w : cohomology (Rep.coind (U : Subgroup G).subtype C) m) :
    inv (shapiroMap U C m) (shapiroMap U C m w) = w :=
  ConcreteCategory.congr_hom (IsIso.hom_inv_id (shapiroMap U C m)) w

theorem cohomologyCores_shapiroMap (A : Rep.{u} k G) [IsDiscreteRep A]
    (w : cohomology (Rep.coind (U : Subgroup G).subtype (Rep.res (U : Subgroup G).subtype A)) p) :
    cohomologyCores U A p (shapiroMap U (Rep.res (U : Subgroup G).subtype A) p w) =
      cohomologyMap (coindTrace (U : Subgroup G) A) p w := by
  rw [cohomologyCores, ConcreteCategory.comp_apply, inv_shapiroMap_apply]

theorem cohomologyCores_cup_cohomologyRes (h : p + q = n)
    (x : cohomology (Rep.res (U : Subgroup G).subtype A) p) (y : cohomology B q) :
    cohomologyCores U (A ⊗ B) n (cohomologyMap (resTensorIso (U : Subgroup G).subtype A B).inv n
        (cup h x (cohomologyRes B U q y))) =
      cup h (cohomologyCores U A p x) y := by
  obtain ⟨z, rfl⟩ : ∃ z, shapiroMap U (Rep.res (U : Subgroup G).subtype A) p z = x :=
    ⟨_, shapiroMap_inv_apply U p x⟩
  have hkey : cohomologyMap (resTensorIso (U : Subgroup G).subtype A B).inv n
      (cup h (shapiroMap U (Rep.res (U : Subgroup G).subtype A) p z) (cohomologyRes B U q y)) =
        shapiroMap U (Rep.res (U : Subgroup G).subtype (A ⊗ B)) n
          (cohomologyMap (coindTensorRight (U : Subgroup G) A B) n (cup h z y)) := by
    rw [shapiroMap_eq, shapiroMap_eq, cohomologyRes_eq, ← cohomologyMapAlong_resTensorHom_cup,
      cohomologyMap_cohomologyMapAlong, cohomologyMapAlong_cohomologyMap,
      coindTensorRight_comp_coindEvalOne]
  rw [hkey, cohomologyCores_shapiroMap, cohomologyCores_shapiroMap, ← ConcreteCategory.comp_apply,
    ← cohomologyMap_comp, coindTensorRight_comp_coindTrace, cohomologyMap_whiskerRight_cup]

end Projection

end GroundTheory.ProfCoh
