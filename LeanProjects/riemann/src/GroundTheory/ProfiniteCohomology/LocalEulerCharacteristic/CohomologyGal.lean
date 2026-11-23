import Mathlib
import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.CohomologyKummer
import GroundTheory.ProfiniteCohomology.LocalClassFormationAlt
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open IntermediateField

variable {K Ksep : Type} [Field K] [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]
  {U V : OpenSubgroup Gal(Ksep/K)} (h : V ≤ U)
  [((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K))).Normal]

noncomputable def fixedFieldGalHom :
    letI := (IntermediateField.inclusion (fixedField_le_fixedField h)).toRingHom.toAlgebra
    (U : Subgroup Gal(Ksep/K)) →* (fixedField (V : Subgroup Gal(Ksep/K)) ≃ₐ[fixedField (U : Subgroup Gal(Ksep/K))]
      fixedField (V : Subgroup Gal(Ksep/K))) :=
  letI := (IntermediateField.inclusion (fixedField_le_fixedField h)).toRingHom.toAlgebra
  { toFun := fun g => AlgEquiv.ofRingEquiv (f := (fixedFieldConj h g).toRingEquiv) fun e =>
      Subtype.ext ((mem_fixedField_iff _ _).1 e.2 g g.2)
    map_one' := AlgEquiv.ext fun _ => Subtype.ext rfl
    map_mul' := fun _ _ => AlgEquiv.ext fun _ => Subtype.ext rfl }

theorem fixedFieldGalHom_surjective : Function.Surjective (fixedFieldGalHom h) := by
  let := (IntermediateField.inclusion (fixedField_le_fixedField h)).toRingHom.toAlgebra
  have : IsScalarTower (fixedField (U : Subgroup Gal(Ksep/K))) (fixedField (V : Subgroup Gal(Ksep/K))) Ksep :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsGalois (fixedField (U : Subgroup Gal(Ksep/K))) Ksep :=
    IsGalois.tower_top_of_isGalois K (fixedField (U : Subgroup Gal(Ksep/K))) Ksep
  intro σ
  set τ := σ.liftNormal Ksep
  have hτU : τ.restrictScalars K ∈ (U : Subgroup Gal(Ksep/K)) :=
    (fixingSubgroup_fixedField_openSubgroup U).le
      ((mem_fixingSubgroup_iff _ _).2 fun x hx => τ.commutes ⟨x, hx⟩)
  exact ⟨⟨τ.restrictScalars K, hτU⟩, AlgEquiv.ext fun x => Subtype.ext (σ.liftNormal_commutes Ksep x)⟩

theorem fixedFieldGalHom_ker :
    (fixedFieldGalHom h).ker = (V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K)) := by
  let := (IntermediateField.inclusion (fixedField_le_fixedField h)).toRingHom.toAlgebra
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro hg
    exact (fixingSubgroup_fixedField_openSubgroup V).le ((mem_fixingSubgroup_iff _ _).2 fun x hx =>
      congrArg Subtype.val (AlgEquiv.ext_iff.1 hg ⟨x, hx⟩))
  · intro hg
    exact AlgEquiv.ext fun x => Subtype.ext ((mem_fixedField_iff _ _).1 x.2 _ hg)

noncomputable def quotientFixedFieldGalEquiv :
    letI := (IntermediateField.inclusion (fixedField_le_fixedField h)).toRingHom.toAlgebra
    (U : Subgroup Gal(Ksep/K)) ⧸ (V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K)) ≃*
      (fixedField (V : Subgroup Gal(Ksep/K)) ≃ₐ[fixedField (U : Subgroup Gal(Ksep/K))]
        fixedField (V : Subgroup Gal(Ksep/K))) :=
  letI := (IntermediateField.inclusion (fixedField_le_fixedField h)).toRingHom.toAlgebra
  (QuotientGroup.quotientMulEquivOfEq (fixedFieldGalHom_ker h).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (fixedFieldGalHom_surjective h))

theorem quotientFixedFieldGalEquiv_mk (g : (U : Subgroup Gal(Ksep/K))) :
    letI := (IntermediateField.inclusion (fixedField_le_fixedField h)).toRingHom.toAlgebra
    quotientFixedFieldGalEquiv h (g : (U : Subgroup Gal(Ksep/K)) ⧸
      (V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K))) = fixedFieldGalHom h g :=
  rfl

theorem cohomologyZeroRootsEquiv_cohomologyConj_gal (l : ℕ) (g : (U : Subgroup Gal(Ksep/K)))
    (x : cohomology (Rep.res ((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K))).subtype
        (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (galRootsOfUnity.{0} K Ksep l))) 0) :
    letI := (IntermediateField.inclusion (fixedField_le_fixedField h)).toRingHom.toAlgebra
    cohomologyZeroRootsEquiv h l ((cohomologyConj (Rep.res (U : Subgroup Gal(Ksep/K)).subtype
        (galRootsOfUnity.{0} K Ksep l)) ((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K))) 0 g).hom x) =
      torsNRep (fixedField (V : Subgroup Gal(Ksep/K)) ≃ₐ[fixedField (U : Subgroup Gal(Ksep/K))]
          fixedField (V : Subgroup Gal(Ksep/K)))
        (Additive (fixedField (V : Subgroup Gal(Ksep/K)))ˣ) l (fixedFieldGalHom h g)
        (cohomologyZeroRootsEquiv h l x) :=
  cohomologyZeroRootsEquiv_cohomologyConj h l g x

theorem cohomologyOneRootsEquiv_cohomologyConj_gal {l : ℕ} (hl : (l : K) ≠ 0) (g : (U : Subgroup Gal(Ksep/K)))
    (x : cohomology (Rep.res ((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K))).subtype
        (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (galRootsOfUnity.{0} K Ksep l))) 1) :
    letI := (IntermediateField.inclusion (fixedField_le_fixedField h)).toRingHom.toAlgebra
    cohomologyOneRootsEquiv h hl ((cohomologyConj (Rep.res (U : Subgroup Gal(Ksep/K)).subtype
        (galRootsOfUnity.{0} K Ksep l)) ((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K))) 1 g).hom x) =
      modNRep (fixedField (V : Subgroup Gal(Ksep/K)) ≃ₐ[fixedField (U : Subgroup Gal(Ksep/K))]
          fixedField (V : Subgroup Gal(Ksep/K)))
        (Additive (fixedField (V : Subgroup Gal(Ksep/K)))ˣ) l (fixedFieldGalHom h g)
        (cohomologyOneRootsEquiv h hl x) := by
  let := (IntermediateField.inclusion (fixedField_le_fixedField h)).toRingHom.toAlgebra
  rw [cohomologyOneRootsEquiv_cohomologyConj]
  obtain ⟨u, hu⟩ := Submodule.mkQ_surjective _ (cohomologyOneRootsEquiv h hl x)
  rw [← hu]
  rfl

end GroundTheory.ProfCoh
