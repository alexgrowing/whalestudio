import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyCoefficientLongExactSequenceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyPullbackPushforwardFunctorialStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory

def coneSES {R : Type} [CommRing R] {C J : Cx R} (u : C ⟶ J) (t : ℤ) : ShortComplex (Shv R) :=
  ShortComplex.mk ((mappingCone.inr u).f t) ((mappingCone.fst u).1.v t (t + 1) rfl) (by simp)

def coneSESSplitting {R : Type} [CommRing R] {C J : Cx R} (u : C ⟶ J) (t : ℤ) : (coneSES u t).Splitting where
  r := (mappingCone.snd u).v t t (add_zero t)
  s := (mappingCone.inl u).v (t + 1) t (by omega)
  f_r := by simp [coneSES]
  s_g := by simp [coneSES]
  id := by
    rw [add_comm]
    exact mappingCone.id_X u t (t + 1) rfl

theorem coneSES_shortExact {R : Type} [CommRing R] {C J : Cx R} (u : C ⟶ J) (t : ℤ) : (coneSES u t).ShortExact :=
  (coneSESSplitting u t).shortExact

theorem sgl_isKInjective {R : Type} [CommRing R] (I : Shv R) [Injective I] : (sgl I).IsKInjective := by
  haveI : ∀ n, Injective ((sgl I).X n) := by
    intro n
    by_cases h : n = 0
    · subst h
      exact Injective.of_iso (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 I).symm inferInstance
    · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 I n h).injective
  exact CochainComplex.isKInjective_of_injective _ 0

theorem sgl_cohomologyClass_subsingleton {R : Type} [CommRing R] (G I : Shv R) (i : ℤ) (hi : i ≠ 0) :
    Subsingleton (CohomologyClass (sgl G) (sgl I) i) := by
  have hc : ∀ a b : Cochain (sgl G) (sgl I) i, a = b := by
    intro a b
    refine Cochain.ext _ _ (fun p q hpq => ?_)
    by_cases hp : p = 0
    · have hq : q ≠ 0 := by omega
      exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 I q hq).eq_of_tgt _ _
    · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 G p hp).eq_of_src _ _
  constructor
  intro x y
  obtain ⟨a, rfl⟩ := x.mk_surjective
  obtain ⟨b, rfl⟩ := y.mk_surjective
  exact congrArg CohomologyClass.mk (Cocycle.ext (hc _ _))

theorem ext_injective_subsingleton {R : Type} [CommRing R] (G I : Shv R) [Injective I] (i : ℤ) (hi : i ≠ 0) :
    Subsingleton (CohomologyClass (sgl G) (res R I) i) := by
  obtain ⟨hK, -, -, hq, -⟩ := GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties R I
  haveI := hK
  haveI := hq
  haveI := sgl_isKInjective I
  obtain ⟨e, he⟩ := (CochainComplex.IsKInjective.quasiIso_iff (resAug I)).1 hq
  have h63 := GlobalTheory.T.hypercohomologyPullbackPushforward_functorial R
  have hsurj : Function.Surjective (cpush (sgl G) (resAug I) i) := by
    intro y
    refine ⟨cpush (sgl G) e.inv i y, ?_⟩
    rw [← h63.2.2.1 (sgl G) e.inv (resAug I) i y, ← he,
      (h63.2.2.2.2 _ _ ⟨e.homotopyInvHomId⟩ (sgl G) i).2, (h63.1 (sgl G) _ i y).2]
  haveI := sgl_cohomologyClass_subsingleton G I i hi
  constructor
  intro x y
  obtain ⟨x', rfl⟩ := hsurj x
  obtain ⟨y', rfl⟩ := hsurj y
  rw [Subsingleton.elim x' y']

theorem cone_terms_ext_subsingleton : ∀ (R : Type) [CommRing R] (G : Shv R) {C J : Cx R} (u : C ⟶ J),
    (∀ t, Injective (J.X t)) → (∀ t i : ℤ, 0 < i → Subsingleton (CohomologyClass (sgl G) (res R (C.X t)) i)) →
    ∀ t i : ℤ, 0 < i → Subsingleton (CohomologyClass (sgl G) (res R ((mappingCone u).X t)) i) := by
  intro R _ G C J u hJ hC t i hi
  obtain ⟨z, hz⟩ := GlobalTheory.T.etaleCohomology_coefficient_longExactSequence R (coneSES u t) (coneSES_shortExact u t)
  have hex := (hz (sgl G) i).1
  haveI := hJ t
  haveI hsJ : Subsingleton (CohomologyClass (sgl G) (res R (J.X t)) i) := ext_injective_subsingleton G (J.X t) i hi.ne'
  haveI hsC : Subsingleton (CohomologyClass (sgl G) (res R (C.X (t + 1))) i) := hC (t + 1) i hi
  constructor
  intro x y
  obtain ⟨w, hw⟩ := (hex x).1 (Subsingleton.elim (α := CohomologyClass (sgl G) (res R (C.X (t + 1))) i) _ _)
  obtain ⟨w', hw'⟩ := (hex y).1 (Subsingleton.elim (α := CohomologyClass (sgl G) (res R (C.X (t + 1))) i) _ _)
  rw [← hw, ← hw', @Subsingleton.elim _ hsJ w w']

end GlobalTheory

end
