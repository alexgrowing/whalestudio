import Mathlib
import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.H0IsoHomCohomologyClassZero
import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.SubsingletonCohomologyOneGalUnitsSubgroupOf
import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.AdditiveDefs
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory IntermediateField

section FixedField

variable {K Ksep : Type} [Field K] [Field Ksep] [Algebra K Ksep]
  {U V : OpenSubgroup Gal(Ksep/K)} (h : V ≤ U)
  [hN : ((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K))).Normal]

include h hN in

theorem inv_mul_mul_mem_of_subgroupOf_normal (g : (U : Subgroup Gal(Ksep/K))) {v : Gal(Ksep/K)}
    (hv : v ∈ (V : Subgroup Gal(Ksep/K))) :
    (g : Gal(Ksep/K))⁻¹ * v * g ∈ (V : Subgroup Gal(Ksep/K)) := by
  have := hN.conj_mem ⟨v, h hv⟩ (Subgroup.mem_subgroupOf.2 hv) g⁻¹
  rw [Subgroup.mem_subgroupOf] at this
  simpa using this

include h hN in

theorem apply_mem_fixedField (g : (U : Subgroup Gal(Ksep/K))) {x : Ksep}
    (hx : x ∈ fixedField (V : Subgroup Gal(Ksep/K))) :
    (g : Gal(Ksep/K)) x ∈ fixedField (V : Subgroup Gal(Ksep/K)) := by
  rw [mem_fixedField_iff] at hx ⊢
  intro v hv
  have e := hx _ (inv_mul_mul_mem_of_subgroupOf_normal h g hv)
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, AlgEquiv.aut_inv] at e
  calc v ((g : Gal(Ksep/K)) x) = (g : Gal(Ksep/K)) ((g : Gal(Ksep/K)).symm (v ((g : Gal(Ksep/K)) x))) :=
        ((g : Gal(Ksep/K)).apply_symm_apply _).symm
    _ = (g : Gal(Ksep/K)) x := by rw [e]

def fixedFieldConj (g : (U : Subgroup Gal(Ksep/K))) :
    fixedField (V : Subgroup Gal(Ksep/K)) ≃ₐ[K] fixedField (V : Subgroup Gal(Ksep/K)) where
  toFun x := ⟨(g : Gal(Ksep/K)) (x : Ksep), apply_mem_fixedField h g x.2⟩
  invFun x := ⟨((g⁻¹ : (U : Subgroup Gal(Ksep/K))) : Gal(Ksep/K)) (x : Ksep), apply_mem_fixedField h g⁻¹ x.2⟩
  left_inv x := Subtype.ext (by
    change ((g⁻¹ : (U : Subgroup Gal(Ksep/K))) : Gal(Ksep/K)) ((g : Gal(Ksep/K)) (x : Ksep)) = x
    rw [Subgroup.coe_inv, ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply])
  right_inv x := Subtype.ext (by
    change (g : Gal(Ksep/K)) (((g⁻¹ : (U : Subgroup Gal(Ksep/K))) : Gal(Ksep/K)) (x : Ksep)) = x
    rw [Subgroup.coe_inv, ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply])
  map_mul' x y := Subtype.ext (map_mul (g : Gal(Ksep/K)) (x : Ksep) y)
  map_add' x y := Subtype.ext (map_add (g : Gal(Ksep/K)) (x : Ksep) y)
  commutes' c := Subtype.ext ((g : Gal(Ksep/K)).commutes c)

@[simp]
theorem coe_fixedFieldConj_apply (g : (U : Subgroup Gal(Ksep/K))) (x : fixedField (V : Subgroup Gal(Ksep/K))) :
    ((fixedFieldConj h g x : fixedField (V : Subgroup Gal(Ksep/K))) : Ksep) = (g : Gal(Ksep/K)) (x : Ksep) :=
  rfl

def fixedFieldConjHom :
    (U : Subgroup Gal(Ksep/K)) →* (fixedField (V : Subgroup Gal(Ksep/K)) ≃ₐ[K] fixedField (V : Subgroup Gal(Ksep/K))) where
  toFun := fixedFieldConj h
  map_one' := AlgEquiv.ext fun _ => Subtype.ext rfl
  map_mul' _ _ := AlgEquiv.ext fun _ => Subtype.ext rfl

@[simp]
theorem fixedFieldConjHom_apply (g : (U : Subgroup Gal(Ksep/K))) :
    fixedFieldConjHom h g = fixedFieldConj h g :=
  rfl

end FixedField

section Invariants

variable {K Ksep : Type} [Field K] [Field Ksep] [Algebra K Ksep]
  {U V : OpenSubgroup Gal(Ksep/K)} (h : V ≤ U)

def unitOfMemFixedField (a : Ksepˣ) (ha : (a : Ksep) ∈ fixedField (V : Subgroup Gal(Ksep/K))) :
    (fixedField (V : Subgroup Gal(Ksep/K)))ˣ :=
  Units.mk0 ⟨a, ha⟩ fun h0 => a.ne_zero (congrArg Subtype.val h0)

@[simp]
theorem coe_unitOfMemFixedField (a : Ksepˣ) (ha : (a : Ksep) ∈ fixedField (V : Subgroup Gal(Ksep/K))) :
    (((unitOfMemFixedField a ha : (fixedField (V : Subgroup Gal(Ksep/K)))ˣ) :
      fixedField (V : Subgroup Gal(Ksep/K))) : Ksep) = a :=
  rfl

include h in

theorem mem_fixedField_of_forall_subgroupOf {x : Ksep}
    (hx : ∀ n : ((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K))),
      ((n : (U : Subgroup Gal(Ksep/K))) : Gal(Ksep/K)) x = x) :
    x ∈ fixedField (V : Subgroup Gal(Ksep/K)) :=
  (mem_fixedField_iff _ _).2 fun v hv => hx ⟨⟨v, h hv⟩, Subgroup.mem_subgroupOf.2 hv⟩

theorem subgroupOf_apply_of_mem_fixedField {x : Ksep} (hx : x ∈ fixedField (V : Subgroup Gal(Ksep/K)))
    (n : ((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K)))) :
    ((n : (U : Subgroup Gal(Ksep/K))) : Gal(Ksep/K)) x = x :=
  (mem_fixedField_iff _ _).1 hx _ (Subgroup.mem_subgroupOf.1 n.2)

noncomputable def unitsInvariantsOpenEquiv :
    Additive (fixedField (V : Subgroup Gal(Ksep/K)))ˣ ≃+
      (Rep.res ((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K))).subtype
        (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (galUnits.{0} K Ksep))).ρ.invariants where
  toFun u := ⟨Additive.ofMul (Units.map (algebraMap (fixedField (V : Subgroup Gal(Ksep/K))) Ksep : _ →* Ksep)
      u.toMul), fun n => congrArg Additive.ofMul (Units.ext
        (subgroupOf_apply_of_mem_fixedField ((u.toMul : fixedField (V : Subgroup Gal(Ksep/K)))).2 n))⟩
  invFun v := Additive.ofMul (unitOfMemFixedField (Additive.toMul (v : Additive Ksepˣ))
    (mem_fixedField_of_forall_subgroupOf h fun n => congrArg (fun w : Additive Ksepˣ => ((w.toMul : Ksepˣ) : Ksep))
      (v.2 n)))
  left_inv _ := Additive.toMul.injective (Units.ext (Subtype.ext rfl))
  right_inv _ := Subtype.ext (Additive.toMul.injective (Units.ext rfl))
  map_add' _ _ := Subtype.ext (Additive.toMul.injective (Units.ext rfl))

@[simp]
theorem coe_unitsInvariantsOpenEquiv_apply (u : Additive (fixedField (V : Subgroup Gal(Ksep/K)))ˣ) :
    (((Additive.toMul ((unitsInvariantsOpenEquiv h u : _) : Additive Ksepˣ)) : Ksepˣ) : Ksep) =
      ((u.toMul : (fixedField (V : Subgroup Gal(Ksep/K)))ˣ) : Ksep) :=
  rfl

noncomputable def rootsInvariantsOpenEquiv (l : ℕ) :
    (Rep.res ((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K))).subtype
        (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (galRootsOfUnity.{0} K Ksep l))).ρ.invariants ≃+
      TorsN (Additive (fixedField (V : Subgroup Gal(Ksep/K)))ˣ) l where
  toFun ζ := ⟨Additive.ofMul (unitOfMemFixedField ((Additive.toMul (ζ : Additive (rootsOfUnity l Ksep)) :
        rootsOfUnity l Ksep) : Ksepˣ)
      (mem_fixedField_of_forall_subgroupOf h fun n => congrArg
        (fun w : Additive (rootsOfUnity l Ksep) => (((w.toMul : rootsOfUnity l Ksep) : Ksepˣ) : Ksep)) (ζ.2 n))),
    (mem_ker_lsmul_iff l _).2 (Additive.toMul.injective (Units.ext (Subtype.ext (by
      change ((((Additive.toMul (ζ : Additive (rootsOfUnity l Ksep)) : rootsOfUnity l Ksep) : Ksepˣ) ^ l :
        Ksepˣ) : Ksep) = 1
      exact (congrArg Units.val ((mem_rootsOfUnity l _).1
        (Additive.toMul (ζ : Additive (rootsOfUnity l Ksep))).2)).trans Units.val_one))))⟩
  invFun x := ⟨Additive.ofMul ⟨Units.map (algebraMap (fixedField (V : Subgroup Gal(Ksep/K))) Ksep : _ →* Ksep)
        ((x : Additive (fixedField (V : Subgroup Gal(Ksep/K)))ˣ).toMul),
      (mem_rootsOfUnity l _).2 (by
        have hx : l • (x : Additive (fixedField (V : Subgroup Gal(Ksep/K)))ˣ) = 0 :=
          (mem_ker_lsmul_iff l _).1 x.2
        rw [← map_pow]
        have : ((x : Additive (fixedField (V : Subgroup Gal(Ksep/K)))ˣ).toMul) ^ l = 1 :=
          congrArg Additive.toMul hx
        rw [this, map_one])⟩,
    fun n => congrArg Additive.ofMul (Subtype.ext (Units.ext
      (subgroupOf_apply_of_mem_fixedField
        (((x : Additive (fixedField (V : Subgroup Gal(Ksep/K)))ˣ).toMul : fixedField (V : Subgroup Gal(Ksep/K)))).2 n)))⟩
  left_inv ζ := Subtype.ext (Additive.toMul.injective (Subtype.ext (Units.ext rfl)))
  right_inv x := Subtype.ext (Additive.toMul.injective (Units.ext (Subtype.ext rfl)))
  map_add' a b := Subtype.ext (Additive.toMul.injective (Units.ext (Subtype.ext rfl)))

@[simp]
theorem coe_rootsInvariantsOpenEquiv_apply (l : ℕ)
    (ζ : (Rep.res ((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K))).subtype
        (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (galRootsOfUnity.{0} K Ksep l))).ρ.invariants) :
    ((((rootsInvariantsOpenEquiv h l ζ : TorsN _ l) : Additive (fixedField (V : Subgroup Gal(Ksep/K)))ˣ).toMul :
      fixedField (V : Subgroup Gal(Ksep/K))) : Ksep) =
      (((Additive.toMul (ζ : Additive (rootsOfUnity l Ksep)) : rootsOfUnity l Ksep) : Ksepˣ) : Ksep) :=
  rfl

end Invariants

section Equivariance

variable {K Ksep : Type} [Field K] [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]
  {U V : OpenSubgroup Gal(Ksep/K)} (h : V ≤ U)

noncomputable def cohomologyZeroRootsEquiv (l : ℕ) :
    cohomology (Rep.res ((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K))).subtype
        (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (galRootsOfUnity.{0} K Ksep l))) 0 ≃+
      TorsN (Additive (fixedField (V : Subgroup Gal(Ksep/K)))ˣ) l :=
  (H0Iso _).toLinearEquiv.toAddEquiv.trans (rootsInvariantsOpenEquiv h l)

variable [((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K))).Normal]

omit [IsSepClosure K Ksep] in

theorem unitsInvariantsOpenEquiv_smul (g : (U : Subgroup Gal(Ksep/K)))
    (u : Additive (fixedField (V : Subgroup Gal(Ksep/K)))ˣ) :
    unitsInvariantsOpenEquiv h (fixedFieldConjHom h g • u) =
      invariantsConj (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (galUnits.{0} K Ksep))
        ((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K))) g (unitsInvariantsOpenEquiv h u) :=
  Subtype.ext (Additive.toMul.injective (Units.ext rfl))

omit [IsSepClosure K Ksep] in

theorem rootsInvariantsOpenEquiv_invariantsConj (l : ℕ) (g : (U : Subgroup Gal(Ksep/K)))
    (ζ : (Rep.res ((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K))).subtype
        (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (galRootsOfUnity.{0} K Ksep l))).ρ.invariants) :
    rootsInvariantsOpenEquiv h l (invariantsConj (Rep.res (U : Subgroup Gal(Ksep/K)).subtype
        (galRootsOfUnity.{0} K Ksep l)) ((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K))) g ζ) =
      torsNRep (fixedField (V : Subgroup Gal(Ksep/K)) ≃ₐ[K] fixedField (V : Subgroup Gal(Ksep/K)))
        (Additive (fixedField (V : Subgroup Gal(Ksep/K)))ˣ) l (fixedFieldConjHom h g)
        (rootsInvariantsOpenEquiv h l ζ) :=
  Subtype.ext (Additive.toMul.injective (Units.ext (Subtype.ext rfl)))

theorem cohomologyZeroRootsEquiv_cohomologyConj (l : ℕ) (g : (U : Subgroup Gal(Ksep/K)))
    (x : cohomology (Rep.res ((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K))).subtype
        (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (galRootsOfUnity.{0} K Ksep l))) 0) :
    cohomologyZeroRootsEquiv h l ((cohomologyConj (Rep.res (U : Subgroup Gal(Ksep/K)).subtype
        (galRootsOfUnity.{0} K Ksep l)) ((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K))) 0 g).hom x) =
      torsNRep (fixedField (V : Subgroup Gal(Ksep/K)) ≃ₐ[K] fixedField (V : Subgroup Gal(Ksep/K)))
        (Additive (fixedField (V : Subgroup Gal(Ksep/K)))ˣ) l (fixedFieldConjHom h g)
        (cohomologyZeroRootsEquiv h l x) := by
  exact (congrArg (rootsInvariantsOpenEquiv h l) (H0Iso_hom_cohomologyConj _ _ g x)).trans
    (rootsInvariantsOpenEquiv_invariantsConj h l g _)

end Equivariance

section Kummer

variable {K Ksep : Type} [Field K] [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]
  {U V : OpenSubgroup Gal(Ksep/K)} (h : V ≤ U) {l : ℕ} (hl : (l : K) ≠ 0)

noncomputable def kummerOpenHom :
    Additive (fixedField (V : Subgroup Gal(Ksep/K)))ˣ →+
      cohomology (Rep.res ((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K))).subtype
        (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (galRootsOfUnity.{0} K Ksep l))) 1 :=
  ((δ (kummerSequenceResRes_shortExact hl (U : Subgroup Gal(Ksep/K))
      ((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K)))) 0 1 rfl).hom.toAddMonoidHom.comp
    (H0Iso (Rep.res ((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K))).subtype
      (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (galUnits.{0} K Ksep)))).inv.hom.toAddMonoidHom).comp
    (unitsInvariantsOpenEquiv h).toAddMonoidHom

theorem kummerOpenHom_apply (u : Additive (fixedField (V : Subgroup Gal(Ksep/K)))ˣ) :
    kummerOpenHom h hl u = (δ (kummerSequenceResRes_shortExact hl (U : Subgroup Gal(Ksep/K))
      ((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K)))) 0 1 rfl).hom
      ((H0Iso (Rep.res ((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K))).subtype
        (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (galUnits.{0} K Ksep)))).inv.hom
        (unitsInvariantsOpenEquiv h u)) :=
  rfl

include hl in

theorem kummerOpenHom_surjective : Function.Surjective (kummerOpenHom (l := l) h hl) := by
  intro x
  obtain ⟨v, hv⟩ := exists_δ_H0Iso_inv_eq (kummerSequenceResRes_shortExact hl (U : Subgroup Gal(Ksep/K))
    ((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K))))
    (subsingleton_cohomology_one_galUnits_subgroupOf h) x
  obtain ⟨u, rfl⟩ := (unitsInvariantsOpenEquiv h).surjective v
  exact ⟨u, hv⟩

include hl in

theorem kummerOpenHom_eq_zero_iff (u : Additive (fixedField (V : Subgroup Gal(Ksep/K)))ˣ) :
    kummerOpenHom h hl u = 0 ↔ ∃ w, l • w = u := by
  rw [kummerOpenHom_apply]
  refine (δ_H0Iso_inv_eq_zero_iff (kummerSequenceResRes_shortExact hl (U : Subgroup Gal(Ksep/K))
    ((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K)))) _).trans ⟨?_, ?_⟩
  · rintro ⟨w, hw⟩
    obtain ⟨w, rfl⟩ := (unitsInvariantsOpenEquiv h).surjective w
    refine ⟨w, (unitsInvariantsOpenEquiv h).injective ?_⟩
    rw [← hw, map_nsmul]
    apply Subtype.ext
    exact (nsmul_id_hom_apply (galUnits.{0} K Ksep) l _).symm
  · rintro ⟨w, rfl⟩
    refine ⟨unitsInvariantsOpenEquiv h w, ?_⟩
    rw [map_nsmul]
    apply Subtype.ext
    exact nsmul_id_hom_apply (galUnits.{0} K Ksep) l _

include hl in
theorem range_lsmul_eq_ker_kummerOpenHom :
    LinearMap.range (LinearMap.lsmul ℤ (Additive (fixedField (V : Subgroup Gal(Ksep/K)))ˣ) (l : ℤ)) =
      LinearMap.ker (kummerOpenHom (l := l) h hl).toIntLinearMap := by
  ext u
  rw [LinearMap.mem_range, LinearMap.mem_ker, AddMonoidHom.coe_toIntLinearMap,
    kummerOpenHom_eq_zero_iff]
  simp only [LinearMap.lsmul_apply, natCast_zsmul]

noncomputable def kummerOpenModNHom :
    ModN (Additive (fixedField (V : Subgroup Gal(Ksep/K)))ˣ) l →ₗ[ℤ]
      cohomology (Rep.res ((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K))).subtype
        (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (galRootsOfUnity.{0} K Ksep l))) 1 :=
  (LinearMap.range (LinearMap.lsmul ℤ (Additive (fixedField (V : Subgroup Gal(Ksep/K)))ˣ) (l : ℤ))).liftQ
    (kummerOpenHom h hl).toIntLinearMap (range_lsmul_eq_ker_kummerOpenHom h hl).le

include hl in
theorem kummerOpenModNHom_bijective : Function.Bijective (kummerOpenModNHom (l := l) h hl) := by
  constructor
  · rw [← LinearMap.ker_eq_bot, kummerOpenModNHom, Submodule.ker_liftQ_eq_bot']
    exact range_lsmul_eq_ker_kummerOpenHom h hl
  · intro x
    obtain ⟨u, rfl⟩ := kummerOpenHom_surjective h hl x
    exact ⟨Submodule.Quotient.mk u, rfl⟩

noncomputable def cohomologyOneRootsEquiv :
    cohomology (Rep.res ((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K))).subtype
        (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (galRootsOfUnity.{0} K Ksep l))) 1 ≃+
      ModN (Additive (fixedField (V : Subgroup Gal(Ksep/K)))ˣ) l :=
  (AddEquiv.ofBijective (kummerOpenModNHom h hl).toAddMonoidHom (kummerOpenModNHom_bijective h hl)).symm

theorem cohomologyOneRootsEquiv_symm_mk (u : Additive (fixedField (V : Subgroup Gal(Ksep/K)))ˣ) :
    (cohomologyOneRootsEquiv h hl).symm (Submodule.Quotient.mk u) = kummerOpenHom h hl u :=
  rfl

theorem cohomologyOneRootsEquiv_kummerOpenHom (u : Additive (fixedField (V : Subgroup Gal(Ksep/K)))ˣ) :
    cohomologyOneRootsEquiv h hl (kummerOpenHom h hl u) = Submodule.Quotient.mk u := by
  rw [← cohomologyOneRootsEquiv_symm_mk, AddEquiv.apply_symm_apply]

variable [((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K))).Normal]

theorem kummerOpenHom_smul (g : (U : Subgroup Gal(Ksep/K)))
    (u : Additive (fixedField (V : Subgroup Gal(Ksep/K)))ˣ) :
    kummerOpenHom h hl (fixedFieldConjHom h g • u) =
      (cohomologyConj (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (galRootsOfUnity.{0} K Ksep l))
        ((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K))) 1 g).hom (kummerOpenHom h hl u) := by
  rw [kummerOpenHom_apply, kummerOpenHom_apply, unitsInvariantsOpenEquiv_smul]
  exact δ_H0Iso_inv_invariantsConj _ (shortExact_map_res (U : Subgroup Gal(Ksep/K))
    (kummerSequence_shortExact l hl)) g _

theorem cohomologyOneRootsEquiv_cohomologyConj (g : (U : Subgroup Gal(Ksep/K)))
    (x : cohomology (Rep.res ((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K))).subtype
        (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (galRootsOfUnity.{0} K Ksep l))) 1) :
    cohomologyOneRootsEquiv h hl ((cohomologyConj (Rep.res (U : Subgroup Gal(Ksep/K)).subtype
        (galRootsOfUnity.{0} K Ksep l)) ((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K))) 1 g).hom x) =
      modNRep (fixedField (V : Subgroup Gal(Ksep/K)) ≃ₐ[K] fixedField (V : Subgroup Gal(Ksep/K)))
        (Additive (fixedField (V : Subgroup Gal(Ksep/K)))ˣ) l (fixedFieldConjHom h g)
        (cohomologyOneRootsEquiv h hl x) := by
  obtain ⟨u, rfl⟩ := kummerOpenHom_surjective h hl x
  rw [← kummerOpenHom_smul, cohomologyOneRootsEquiv_kummerOpenHom, cohomologyOneRootsEquiv_kummerOpenHom,
    modNRep_mk]

end Kummer

end GroundTheory.ProfCoh
