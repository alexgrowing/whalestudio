import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BijectiveAlgebraMapIntegralClosureOfBirational

open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem bijective_of_existsUnique_field_point {S T : Scheme.{0}} (f : S ⟶ T)
    (h : ∀ (k : Type) [Field k] (w : Sp k ⟶ T), ∃! z : Sp k ⟶ S, z ≫ f = w) :
    Function.Bijective f := by
  constructor
  · intro x x' hx
    obtain ⟨z, hz, hz'⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := f) x x' hx
    let p : Sp ((pullback f f).residueField z) ⟶ pullback f f :=
      (pullback f f).fromSpecResidueField z
    have e : p ≫ pullback.fst f f = p ≫ pullback.snd f f :=
      (h _ (p ≫ pullback.fst f f ≫ f)).unique (by simp) (by simp [pullback.condition])
    let a : Sp ((pullback f f).residueField z) := IsLocalRing.closedPoint _
    have ha : p a = z := Scheme.fromSpecResidueField_apply z a
    have e' : (p ≫ pullback.fst f f) a = (p ≫ pullback.snd f f) a := by rw [e]
    rwa [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, ha, hz, hz'] at e'
  · intro t
    obtain ⟨z, hz, -⟩ := h (T.residueField t) (T.fromSpecResidueField t)
    let a : Sp (T.residueField t) := IsLocalRing.closedPoint _
    refine ⟨z a, ?_⟩
    rw [← Scheme.Hom.comp_apply, hz]
    exact Scheme.fromSpecResidueField_apply t a

theorem existsUnique_field_point_morphismRestrict {S T : Scheme.{0}} (f : S ⟶ T)
    (h : ∀ (k : Type) [Field k] (w : Sp k ⟶ T), ∃! z : Sp k ⟶ S, z ≫ f = w) (V : T.Opens)
    (k : Type) [Field k] (w : Sp k ⟶ V) : ∃! z : Sp k ⟶ (f ⁻¹ᵁ V), z ≫ (f ∣_ V) = w := by
  obtain ⟨z, hz, hu⟩ := h k (w ≫ V.ι)
  have P := (isPullback_morphismRestrict f V).flip
  refine ⟨P.lift z w hz, P.lift_snd _ _ _, fun y hy ↦ ?_⟩
  apply P.hom_ext
  · rw [P.lift_fst]
    apply hu
    show (y ≫ _) ≫ f = _
    rw [Category.assoc, ← morphismRestrict_ι, ← Category.assoc, hy]
  · rw [P.lift_snd]; exact hy

theorem isIso_stalkMap_genericPoint_of_lift {S T : Scheme.{0}} (f : S ⟶ T) [IsIntegral S]
    [IsIntegral T] [IsDominant f] (hf : Function.Injective f)
    (z : Spec T.functionField ⟶ S) (hz : z ≫ f = T.fromSpecStalk (genericPoint T)) :
    IsIso (f.stalkMap (genericPoint S)) := by
  have hs : z (IsLocalRing.closedPoint _) = genericPoint S := by
    apply hf
    rw [apply_genericPoint_of_isDominant f]
    refine (Scheme.Hom.comp_apply z f _).symm.trans ?_
    rw [hz]
    exact Scheme.fromSpecStalk_closedPoint
  have hF : IsField (S.presheaf.stalk (z (IsLocalRing.closedPoint _))) := by
    rw [hs]; exact Field.toIsField S.functionField
  rw [← hs]
  have h1 : IsIso (Scheme.stalkClosedPointTo (z ≫ f)) := by
    rw [hz, Scheme.stalkClosedPointTo_fromSpecStalk]
    infer_instance
  rw [Scheme.stalkClosedPointTo_comp] at h1
  have h2 : IsIso (Scheme.stalkClosedPointTo z) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    constructor
    · letI := hF.toField
      exact (Scheme.stalkClosedPointTo z).hom.injective
    · intro y
      obtain ⟨x, hx⟩ := (@ConcreteCategory.bijective_of_isIso _ _ _ _ _ _ _ _ _ h1).2 y
      exact ⟨_, hx⟩
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ (Scheme.stalkClosedPointTo z) h2 h1

theorem isIso_of_isProper_of_existsUnique_field_point_of_isIntegral {S T : Scheme.{0}} (f : S ⟶ T)
    [IsProper f] [IsReduced S] [IsIntegral T] [GlobalTheory.IsNormalScheme T]
    (h : ∀ (k : Type) [Field k] (w : Sp k ⟶ T), ∃! z : Sp k ⟶ S, z ≫ f = w) : IsIso f := by
  have hb := bijective_of_existsUnique_field_point f h
  have hh : IsHomeomorph f :=
    isHomeomorph_iff_continuous_isClosedMap_bijective.mpr ⟨f.continuous, f.isClosedMap, hb⟩
  have : IrreducibleSpace S := hh.homeomorph.symm.irreducibleSpace_iff.mp inferInstance
  have : IsIntegral S := isIntegral_of_irreducibleSpace_of_isReduced S
  have : IsDominant f := ⟨hb.2.denseRange⟩
  have : LocallyQuasiFinite f := LocallyQuasiFinite.of_finite_preimage_singleton f
    fun t ↦ (Set.finite_singleton t).preimage hb.1.injOn
  obtain ⟨z, hz, -⟩ := h T.functionField (T.fromSpecStalk (genericPoint T))
  have := isIso_stalkMap_genericPoint_of_lift f hb.1 z hz
  exact isIso_of_isProper_of_quasiFinite_of_isIso_stalkMap f fun _ ↦ inferInstance

theorem isIso_of_isProper_of_existsUnique_field_point (S T : Scheme.{0}) (f : S ⟶ T)
    (hf : IsProper f) (hS : IsReduced S) (hT : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme T)
    (hN : IsLocallyNoetherian T)
    (h : ∀ (k : Type) [Field k] (w : Sp k ⟶ T), ∃! z : Sp k ⟶ S, z ≫ f = w) : IsIso f := by
  have := GlobalTheory.IsNormalScheme.of_pred hT
  refine (IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := .isomorphisms _)
    GlobalTheory.IsNormalScheme.component (GlobalTheory.IsNormalScheme.iSup_component T)).mpr fun Z ↦ ?_
  exact isIso_of_isProper_of_existsUnique_field_point_of_isIntegral
    (f ∣_ GlobalTheory.IsNormalScheme.component Z) (existsUnique_field_point_morphismRestrict f h _)

end GlobalTheory
