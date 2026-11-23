import Mathlib
import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.H0IsoHomCohomologyClassZero
import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.AdditiveSnake
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory

universe u

noncomputable section

section Sequence

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (N : Subgroup G) {T O : Rep.{u} (ULift.{u} ℤ) G} [IsDiscreteRep T] [IsDiscreteRep O]
  {n : ℕ} {f : T ⟶ O} {w : f ≫ (n • 𝟙 O) = 0} (hS : (ShortComplex.mk f (n • 𝟙 O) w).ShortExact)

theorem cohomologyMap_res_nsmul_apply (O : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep O] (n i : ℕ)
    (x : cohomology (Rep.res N.subtype O) i) :
    (cohomologyMap ((Rep.resFunctor N.subtype).map (n • 𝟙 O)) i).hom x = n • x := by
  rw [Functor.map_nsmul, CategoryTheory.Functor.map_id]
  exact cohomologyMap_nsmul_id_apply _ n i x

set_option linter.unusedSectionVars false in
include hS in

theorem nsmul_cohomologyMap_res_f_apply (i : ℕ) (x : cohomology (Rep.res N.subtype T) i) :
    n • (cohomologyMap ((Rep.resFunctor N.subtype).map f) i).hom x = 0 := by
  rw [← cohomologyMap_res_nsmul_apply N O n i]
  exact cohomologyMap_g_cohomologyMap_f_apply
    (S := (ShortComplex.mk f (n • 𝟙 O) w).map (Rep.resFunctor N.subtype)) i x

theorem δ_res_nsmul_apply (i : ℕ) (y : cohomology (Rep.res N.subtype O) i) :
    (δ (shortExact_map_res N hS) i (i + 1) rfl).hom (n • y) = 0 := by
  rw [← cohomologyMap_res_nsmul_apply N O n i]
  exact congrArg (fun φ => φ.hom y) (comp_δ (shortExact_map_res N hS) i (i + 1) rfl)

def kummerResδ (i : ℕ) : cohomology (Rep.res N.subtype O) i →+ cohomology (Rep.res N.subtype T) (i + 1) :=
  (δ (shortExact_map_res N hS) i (i + 1) rfl).hom.toAddMonoidHom

theorem kummerResδ_apply (i : ℕ) (y : cohomology (Rep.res N.subtype O) i) :
    kummerResδ N hS i y = (δ (shortExact_map_res N hS) i (i + 1) rfl).hom y :=
  rfl

def kummerTorsHom (i : ℕ) :
    cohomology (Rep.res N.subtype T) i →+ TorsN (cohomology (Rep.res N.subtype O) i) n where
  toFun x := ⟨(cohomologyMap ((Rep.resFunctor N.subtype).map f) i).hom x,
    (mem_ker_lsmul_iff n _).2 (nsmul_cohomologyMap_res_f_apply N hS i x)⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

@[simp]
theorem coe_kummerTorsHom_apply (i : ℕ) (x : cohomology (Rep.res N.subtype T) i) :
    ((kummerTorsHom N hS i x : TorsN _ n) : cohomology (Rep.res N.subtype O) i) =
      (cohomologyMap ((Rep.resFunctor N.subtype).map f) i).hom x :=
  rfl

include hS in
theorem range_lsmul_le_ker_δ (i : ℕ) :
    LinearMap.range (LinearMap.lsmul ℤ (cohomology (Rep.res N.subtype O) i) (n : ℤ)) ≤
      LinearMap.ker (kummerResδ N hS i).toIntLinearMap := by
  rintro _ ⟨y, rfl⟩
  rw [LinearMap.mem_ker, LinearMap.lsmul_apply, natCast_zsmul, AddMonoidHom.coe_toIntLinearMap]
  exact δ_res_nsmul_apply N hS i y

def kummerModNHom (i : ℕ) :
    ModN (cohomology (Rep.res N.subtype O) i) n →+ cohomology (Rep.res N.subtype T) (i + 1) :=
  ((LinearMap.range (LinearMap.lsmul ℤ (cohomology (Rep.res N.subtype O) i) (n : ℤ))).liftQ
    (kummerResδ N hS i).toIntLinearMap
    (range_lsmul_le_ker_δ N hS i)).toAddMonoidHom

include hS in
theorem range_lsmul_eq_ker_δ (i : ℕ) :
    LinearMap.range (LinearMap.lsmul ℤ (cohomology (Rep.res N.subtype O) i) (n : ℤ)) =
      LinearMap.ker (kummerResδ N hS i).toIntLinearMap := by
  refine le_antisymm (range_lsmul_le_ker_δ N hS i) fun y hy => ?_
  rw [LinearMap.mem_ker, AddMonoidHom.coe_toIntLinearMap, kummerResδ_apply] at hy
  obtain ⟨z, hz⟩ := (ShortComplex.moduleCat_exact_iff _).1
    (cohomology_exact₃ (shortExact_map_res N hS) i (i + 1) rfl) y hy
  let z' : cohomology (Rep.res N.subtype O) i := z
  have hz' : (cohomologyMap ((Rep.resFunctor N.subtype).map (n • 𝟙 O)) i).hom z' = y := hz
  refine ⟨z', ?_⟩
  change (n : ℤ) • z' = y
  rw [natCast_zsmul, ← cohomologyMap_res_nsmul_apply N O n i]
  exact hz'

theorem kummerModNHom_injective (i : ℕ) : Function.Injective (kummerModNHom N hS i) := by
  change Function.Injective ((LinearMap.range (LinearMap.lsmul ℤ
    (cohomology (Rep.res N.subtype O) i) (n : ℤ))).liftQ
    (kummerResδ N hS i).toIntLinearMap
    (range_lsmul_le_ker_δ N hS i))
  rw [← LinearMap.ker_eq_bot, Submodule.ker_liftQ_eq_bot']
  exact range_lsmul_eq_ker_δ N hS i

theorem kummerTorsHom_surjective (i : ℕ) : Function.Surjective (kummerTorsHom N hS i) := by
  rintro ⟨y, hy⟩
  have hy' : (cohomologyMap ((Rep.resFunctor N.subtype).map (n • 𝟙 O)) i).hom y = 0 := by
    rw [cohomologyMap_res_nsmul_apply]
    exact (mem_ker_lsmul_iff n y).1 hy
  obtain ⟨x, hx⟩ := exists_cohomologyMap_f_eq (shortExact_map_res N hS) i y hy'
  exact ⟨x, Subtype.ext hx⟩

theorem kummerTorsHom_eq_zero_iff (i : ℕ) (x : cohomology (Rep.res N.subtype T) (i + 1)) :
    kummerTorsHom N hS (i + 1) x = 0 ↔ ∃ y, kummerModNHom N hS i y = x := by
  constructor
  · intro hx
    have hx' : (cohomologyMap ((Rep.resFunctor N.subtype).map f) (i + 1)).hom x = 0 :=
      congrArg Subtype.val hx
    obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff _).1
      (cohomology_exact₁ (shortExact_map_res N hS) i (i + 1) rfl) x hx'
    exact ⟨Submodule.Quotient.mk y, hy⟩
  · rintro ⟨y, rfl⟩
    induction y using Submodule.Quotient.induction_on with
    | H y =>
      apply Subtype.ext
      exact congrArg (fun φ => φ.hom y) (δ_comp (shortExact_map_res N hS) i (i + 1) rfl)

include hS in

theorem cohomologyMap_res_f_injective_zero :
    Function.Injective (cohomologyMap ((Rep.resFunctor N.subtype).map f) 0).hom := by
  have hf : Function.Injective f.hom := (Rep.mono_iff_injective f).1 hS.mono_f
  intro x y hxy
  have e := fun z => congrArg (fun φ => φ.hom z)
    (cohomologyMap_zero_comp_H0Iso_hom ((Rep.resFunctor N.subtype).map f))
  have h1 := (e x).symm.trans ((congrArg (H0Iso (Rep.res N.subtype O)).hom.hom hxy).trans (e y))
  have h2 : (H0Iso (Rep.res N.subtype T)).hom.hom x = (H0Iso (Rep.res N.subtype T)).hom.hom y :=
    Subtype.ext (hf (congrArg Subtype.val h1))
  rw [← H0Iso_inv_hom_apply _ x, h2, H0Iso_inv_hom_apply]

theorem kummerTorsHom_bijective_zero : Function.Bijective (kummerTorsHom N hS 0) :=
  ⟨fun _ _ hxy => cohomologyMap_res_f_injective_zero N hS (congrArg Subtype.val hxy),
    kummerTorsHom_surjective N hS 0⟩

variable [N.Normal]

theorem kummerTorsHom_cohomologyConj (i : ℕ) (g : G) (x : cohomology (Rep.res N.subtype T) i) :
    ((kummerTorsHom N hS i ((cohomologyConj T N i g).hom x) : TorsN _ n) :
        cohomology (Rep.res N.subtype O) i) =
      (cohomologyConj O N i g).hom (kummerTorsHom N hS i x) :=
  (congrArg (fun φ => φ.hom x) (cohomologyConj_naturality T N f i g)).symm

theorem kummerModNHom_cohomologyConj (i : ℕ) (g : G) (y : cohomology (Rep.res N.subtype O) i) :
    kummerModNHom N hS i (Submodule.Quotient.mk ((cohomologyConj O N i g).hom y)) =
      (cohomologyConj T N (i + 1) g).hom (kummerModNHom N hS i (Submodule.Quotient.mk y)) :=
  (congrArg (fun φ => φ.hom y) (δ_comp_cohomologyConj N hS i (i + 1) rfl g)).symm

end Sequence

section Action

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (N : Subgroup G) [N.Normal] [CompactSpace N] {Γ : Type*} [Group Γ] (π : G →* Γ)
  (hπ : Function.Surjective π) (hker : π.ker ≤ N)

include hker in

theorem cohomologyConj_eq_of_map_eq (A : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep A] (i : ℕ)
    {g h : G} (hgh : π g = π h) : cohomologyConj A N i g = cohomologyConj A N i h := by
  refine cohomologyConj_eq_of_mk_eq A N i (QuotientGroup.eq.2 (hker ?_))
  rw [MonoidHom.mem_ker, map_mul, map_inv, hgh, inv_mul_cancel]

@[reducible] def conjActionOf (A : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep A] (i : ℕ) :
    DistribMulAction Γ (cohomology (Rep.res N.subtype A) i) where
  smul γ x := (cohomologyConj A N i (Function.surjInv hπ γ)).hom x
  one_smul x := by
    change (cohomologyConj A N i (Function.surjInv hπ 1)).hom x = x
    rw [cohomologyConj_eq_of_map_eq N π hker A i (h := 1)
      ((Function.surjInv_eq hπ 1).trans (map_one π).symm), cohomologyConj_one]
    rfl
  mul_smul γ δ x := by
    change (cohomologyConj A N i (Function.surjInv hπ (γ * δ))).hom x =
      (cohomologyConj A N i (Function.surjInv hπ γ)).hom
        ((cohomologyConj A N i (Function.surjInv hπ δ)).hom x)
    rw [cohomologyConj_eq_of_map_eq N π hker A i (h := Function.surjInv hπ γ * Function.surjInv hπ δ)
      (by rw [map_mul, Function.surjInv_eq hπ, Function.surjInv_eq hπ, Function.surjInv_eq hπ]),
      cohomologyConj_mul_apply]
  smul_zero _ := map_zero _
  smul_add _ _ _ := map_add _ _ _

theorem conjActionOf_smul (A : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep A] (i : ℕ) (g : G)
    (x : cohomology (Rep.res N.subtype A) i) :
    (letI := conjActionOf N π hπ hker A i; π g • x) = (cohomologyConj A N i g).hom x :=
  congrArg (fun φ => φ.hom x)
    (cohomologyConj_eq_of_map_eq N π hker A i (Function.surjInv_eq hπ (π g)))

variable {T O : Rep.{u} (ULift.{u} ℤ) G} [IsDiscreteRep T] [IsDiscreteRep O]
  {l : ℕ} {f : T ⟶ O} {w : f ≫ (l • 𝟙 O) = 0} (hS : (ShortComplex.mk f (l • 𝟙 O) w).ShortExact)

include hS in

theorem toFun_eq_modN_add_torsN (d : AdditiveFunction.{u} l Γ) (i : ℕ)
    [Finite (ModN (cohomology (Rep.res N.subtype O) i) l)]
    [Finite (TorsN (cohomology (Rep.res N.subtype O) (i + 1)) l)]
    {X : Type u} [AddCommGroup X] [Module (ZMod l) X] [Finite X] (ρX : Representation (ZMod l) Γ X)
    (e : X ≃+ cohomology (Rep.res N.subtype T) (i + 1))
    (he : ∀ (g : G) (x : X), e (ρX (π g) x) = (cohomologyConj T N (i + 1) g).hom (e x)) :
    d.toFun X ρX =
      (letI := conjActionOf N π hπ hker O i;
        d.toFun (ModN (cohomology (Rep.res N.subtype O) i) l)
          (modNRep Γ (cohomology (Rep.res N.subtype O) i) l)) +
      (letI := conjActionOf N π hπ hker O (i + 1);
        d.toFun (TorsN (cohomology (Rep.res N.subtype O) (i + 1)) l)
          (torsNRep Γ (cohomology (Rep.res N.subtype O) (i + 1)) l)) := by
  let := conjActionOf N π hπ hker O i
  let := conjActionOf N π hπ hker O (i + 1)
  have he' : ∀ (g : G) (y : cohomology (Rep.res N.subtype T) (i + 1)),
      e.symm ((cohomologyConj T N (i + 1) g).hom y) = ρX (π g) (e.symm y) := fun g y => by
    apply e.injective
    rw [he, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  let φ : ModN (cohomology (Rep.res N.subtype O) i) l →ₗ[ZMod l] X :=
    ((e.symm.toAddMonoidHom).comp (kummerModNHom N hS i)).toZModLinearMap l
  let ψ : X →ₗ[ZMod l] TorsN (cohomology (Rep.res N.subtype O) (i + 1)) l :=
    ((kummerTorsHom N hS (i + 1)).comp e.toAddMonoidHom).toZModLinearMap l
  refine d.additive _ ρX _ φ ψ ⟨fun γ y => ?_⟩ ⟨fun γ x => ?_⟩ ?_ ?_ ?_
  · obtain ⟨g, rfl⟩ := hπ γ
    induction y using Submodule.Quotient.induction_on with
    | H y =>
      change e.symm (kummerModNHom N hS i (Submodule.Quotient.mk (π g • y))) =
        ρX (π g) (e.symm (kummerModNHom N hS i (Submodule.Quotient.mk y)))
      rw [conjActionOf_smul, kummerModNHom_cohomologyConj, he']
  · obtain ⟨g, rfl⟩ := hπ γ
    apply Subtype.ext
    change ((kummerTorsHom N hS (i + 1) (e (ρX (π g) x)) : TorsN _ l) :
        cohomology (Rep.res N.subtype O) (i + 1)) =
      π g • ((kummerTorsHom N hS (i + 1) (e x) : TorsN _ l) : cohomology (Rep.res N.subtype O) (i + 1))
    rw [he, kummerTorsHom_cohomologyConj, conjActionOf_smul]
  · exact e.symm.injective.comp (kummerModNHom_injective N hS i)
  · intro x
    constructor
    · intro hx
      obtain ⟨y, hy⟩ := (kummerTorsHom_eq_zero_iff N hS i (e x)).1 hx
      refine ⟨y, ?_⟩
      change e.symm (kummerModNHom N hS i y) = x
      rw [hy, AddEquiv.symm_apply_apply]
    · rintro ⟨y, rfl⟩
      change kummerTorsHom N hS (i + 1) (e (e.symm (kummerModNHom N hS i y))) = 0
      rw [AddEquiv.apply_symm_apply]
      exact (kummerTorsHom_eq_zero_iff N hS i _).2 ⟨y, rfl⟩
  · intro z
    obtain ⟨x, hx⟩ := kummerTorsHom_surjective N hS (i + 1) z
    exact ⟨e.symm x, by
      change kummerTorsHom N hS (i + 1) (e (e.symm x)) = z
      rw [AddEquiv.apply_symm_apply, hx]⟩

include hS in

theorem toFun_eq_torsN_zero (d : AdditiveFunction.{u} l Γ)
    [Finite (TorsN (cohomology (Rep.res N.subtype O) 0) l)]
    {X : Type u} [AddCommGroup X] [Module (ZMod l) X] [Finite X] (ρX : Representation (ZMod l) Γ X)
    (e : X ≃+ cohomology (Rep.res N.subtype T) 0)
    (he : ∀ (g : G) (x : X), e (ρX (π g) x) = (cohomologyConj T N 0 g).hom (e x)) :
    d.toFun X ρX =
      (letI := conjActionOf N π hπ hker O 0;
        d.toFun (TorsN (cohomology (Rep.res N.subtype O) 0) l)
          (torsNRep Γ (cohomology (Rep.res N.subtype O) 0) l)) := by
  let := conjActionOf N π hπ hker O 0
  let E : X ≃+ TorsN (cohomology (Rep.res N.subtype O) 0) l :=
    e.trans (AddEquiv.ofBijective (kummerTorsHom N hS 0) (kummerTorsHom_bijective_zero N hS))
  refine d.toFun_congr _ _
    { (E.toAddMonoidHom.toZModLinearMap l) with
      invFun := E.symm, left_inv := E.left_inv, right_inv := E.right_inv } fun γ x => ?_
  obtain ⟨g, rfl⟩ := hπ γ
  apply Subtype.ext
  change ((kummerTorsHom N hS 0 (e (ρX (π g) x)) : TorsN _ l) : cohomology (Rep.res N.subtype O) 0) =
    π g • ((kummerTorsHom N hS 0 (e x) : TorsN _ l) : cohomology (Rep.res N.subtype O) 0)
  rw [he, kummerTorsHom_cohomologyConj, conjActionOf_smul]

end Action

end

end GroundTheory.ProfCoh
