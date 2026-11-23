import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ExpRowsPf
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

noncomputable section

namespace PositivityTheory.Xgf.TwoTangentVectors

abbrev D2 : Type := DualNumber (DualNumber ℂ)

def i1 : DualNumber ℂ →+* D2 := algebraMap (DualNumber ℂ) D2

def i2 : DualNumber ℂ →+* D2 := dualMap (algebraMap ℂ (DualNumber ℂ))

def r1 : D2 →+* DualNumber ℂ := (TrivSqZeroExt.fstHom (DualNumber ℂ) (DualNumber ℂ) (DualNumber ℂ)).toRingHom

def r2 : D2 →+* DualNumber ℂ := dualMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom

def q : D2 →+* DualNumber ℂ where
  toFun x := x.fst + TrivSqZeroExt.inr x.snd.fst
  map_one' := by ext <;> simp
  map_mul' a b := by
    ext <;> simp [TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul] <;> ring
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp <;> ring

theorem algebraMap_doubleDual_apply (a : ℂ) : algebraMap ℂ D2 a = TrivSqZeroExt.inl (TrivSqZeroExt.inl a) := rfl

theorem q_snd (a : D2) : (q a).snd = (r1 a).snd + (r2 a).snd := by
  simp [q, r1, r2, dualMap]

theorem quotient_inclusion_one : q.comp i1 = RingHom.id _ := by
  ext a <;> simp [q, i1, TrivSqZeroExt.algebraMap_eq_inl, algebraMap_doubleDual_apply]
theorem quotient_inclusion_two : q.comp i2 = RingHom.id _ := by
  ext a <;> simp [q, i2, dualMap, TrivSqZeroExt.algebraMap_eq_inl, algebraMap_doubleDual_apply]
theorem retraction_one_inclusion_one : r1.comp i1 = RingHom.id _ := by
  ext a <;> simp [r1, i1, TrivSqZeroExt.algebraMap_eq_inl, algebraMap_doubleDual_apply]
theorem retraction_one_inclusion_two : r1.comp i2 = GlobalTheory.CompanionTheory.Ar.epsMul 0 := by
  ext a <;> simp [r1, i2, dualMap, GlobalTheory.CompanionTheory.Ar.epsMul, TrivSqZeroExt.algebraMap_eq_inl, algebraMap_doubleDual_apply]
theorem retraction_two_inclusion_one : r2.comp i1 = GlobalTheory.CompanionTheory.Ar.epsMul 0 := by
  ext a <;> simp [r2, i1, dualMap, GlobalTheory.CompanionTheory.Ar.epsMul, TrivSqZeroExt.algebraMap_eq_inl, algebraMap_doubleDual_apply]
theorem retraction_two_inclusion_two : r2.comp i2 = RingHom.id _ := by
  ext a <;> simp [r2, i2, dualMap, TrivSqZeroExt.algebraMap_eq_inl, algebraMap_doubleDual_apply]
theorem inclusion_one_algebraMap : i1.comp (algebraMap ℂ (DualNumber ℂ)) = algebraMap ℂ D2 := by
  ext a <;> simp [i1, TrivSqZeroExt.algebraMap_eq_inl, algebraMap_doubleDual_apply]
theorem inclusion_two_algebraMap : i2.comp (algebraMap ℂ (DualNumber ℂ)) = algebraMap ℂ D2 := by
  ext a <;> simp [i2, dualMap, TrivSqZeroExt.algebraMap_eq_inl, algebraMap_doubleDual_apply]
theorem q_alg : q.comp (algebraMap ℂ D2) = algebraMap ℂ (DualNumber ℂ) := by
  ext a <;> simp [q, TrivSqZeroExt.algebraMap_eq_inl, algebraMap_doubleDual_apply]
theorem retraction_one_algebraMap : r1.comp (algebraMap ℂ D2) = algebraMap ℂ (DualNumber ℂ) := by
  ext a <;> simp [r1, TrivSqZeroExt.algebraMap_eq_inl, algebraMap_doubleDual_apply]
theorem retraction_two_algebraMap : r2.comp (algebraMap ℂ D2) = algebraMap ℂ (DualNumber ℂ) := by
  ext a <;> simp [r2, dualMap, TrivSqZeroExt.algebraMap_eq_inl, algebraMap_doubleDual_apply]

instance : IsLocalRing (DualNumber ℂ) := LieTangent.isLocalRing_dual
instance : IsLocalRing D2 := LieTangent.isLocalRing_dual

instance : IsLocalHom q :=
  ⟨fun a ha => by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst]
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst] at ha
    have : (q a).fst = a.fst.fst := by simp [q]
    rw [this] at ha
    exact TrivSqZeroExt.isUnit_iff_isUnit_fst.2 ha⟩

section Sch

variable {X : Scheme.{0}} {G : Over X} [GrpObj G] (x : Sp ℂ ⟶ X)

abbrev W2 : Over X := Over.mk (spMap (algebraMap ℂ D2) ≫ x)

def p1 : W2 x ⟶ epsAt x := Over.homMk (spMap i1) (by
  show spMap i1 ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ (DualNumber ℂ))) ≫ x = spMap (algebraMap ℂ D2) ≫ x
  rw [← Category.assoc, LieTangent.spec_comp, inclusion_one_algebraMap])
def p2 : W2 x ⟶ epsAt x := Over.homMk (spMap i2) (by
  show spMap i2 ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ (DualNumber ℂ))) ≫ x = spMap (algebraMap ℂ D2) ≫ x
  rw [← Category.assoc, LieTangent.spec_comp, inclusion_two_algebraMap])
def mQ : epsAt x ⟶ W2 x := Over.homMk (spMap q) (by
  show spMap q ≫ spMap (algebraMap ℂ D2) ≫ x = Spec.map (CommRingCat.ofHom (algebraMap ℂ (DualNumber ℂ))) ≫ x
  rw [← Category.assoc, LieTangent.spec_comp, q_alg])
def retractionOne : epsAt x ⟶ W2 x := Over.homMk (spMap r1) (by
  show spMap r1 ≫ spMap (algebraMap ℂ D2) ≫ x = Spec.map (CommRingCat.ofHom (algebraMap ℂ (DualNumber ℂ))) ≫ x
  rw [← Category.assoc, LieTangent.spec_comp, retraction_one_algebraMap])
def retractionTwo : epsAt x ⟶ W2 x := Over.homMk (spMap r2) (by
  show spMap r2 ≫ spMap (algebraMap ℂ D2) ≫ x = Spec.map (CommRingCat.ofHom (algebraMap ℂ (DualNumber ℂ))) ≫ x
  rw [← Category.assoc, LieTangent.spec_comp, retraction_two_algebraMap])

theorem spec_id' : Spec.map (CommRingCat.ofHom (RingHom.id (DualNumber ℂ))) = 𝟙 _ := by
  rw [CommRingCat.ofHom_id, Spec.map_id]

theorem quotient_projection_one : mQ x ≫ p1 x = 𝟙 _ := Over.OverMorphism.ext (by
  show spMap q ≫ spMap i1 = 𝟙 _
  rw [LieTangent.spec_comp, quotient_inclusion_one, spec_id'])
theorem quotient_projection_two : mQ x ≫ p2 x = 𝟙 _ := Over.OverMorphism.ext (by
  show spMap q ≫ spMap i2 = 𝟙 _
  rw [LieTangent.spec_comp, quotient_inclusion_two, spec_id'])
theorem retraction_one_projection_one : retractionOne x ≫ p1 x = 𝟙 _ := Over.OverMorphism.ext (by
  show spMap r1 ≫ spMap i1 = 𝟙 _
  rw [LieTangent.spec_comp, retraction_one_inclusion_one, spec_id'])
theorem retraction_one_projection_two : retractionOne x ≫ p2 x = LieTangent.epsScale x 0 := Over.OverMorphism.ext (by
  show spMap r1 ≫ spMap i2 = Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.epsMul 0))
  rw [LieTangent.spec_comp, retraction_one_inclusion_two])
theorem retraction_two_projection_one : retractionTwo x ≫ p1 x = LieTangent.epsScale x 0 := Over.OverMorphism.ext (by
  show spMap r2 ≫ spMap i1 = Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.epsMul 0))
  rw [LieTangent.spec_comp, retraction_two_inclusion_one])
theorem retraction_two_projection_two : retractionTwo x ≫ p2 x = 𝟙 _ := Over.OverMorphism.ext (by
  show spMap r2 ≫ spMap i2 = 𝟙 _
  rw [LieTangent.spec_comp, retraction_two_inclusion_two, spec_id'])

omit [GrpObj G] in
theorem scale0 [GrpObj G] {v : epsAt x ⟶ G} (hv : IsTanAt G x v) : LieTangent.epsScale x 0 ≫ v = 1 := by
  let pr : epsAt x ⟶ Over.mk x := Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap ℂ (DualNumber ℂ)))) rfl
  have e : LieTangent.epsScale x 0 = pr ≫ LieTangent.epsZero x := Over.OverMorphism.ext (by
    show Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.epsMul 0)) =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (DualNumber ℂ))) ≫
        Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom)
    rw [LieTangent.spec_comp]
    congr 2
    ext a <;> simp [GlobalTheory.CompanionTheory.Ar.epsMul, TrivSqZeroExt.algebraMap_eq_inl])
  rw [e, Category.assoc, (LieTangent.isTanAt_iff _).1 hv, MonObj.comp_one]

def V2 (v v' : epsAt x ⟶ G) : W2 x ⟶ G := (p1 x ≫ v) * (p2 x ≫ v')

theorem quotient_tangent_product (v v' : epsAt x ⟶ G) : mQ x ≫ V2 x v v' = v * v' := by
  rw [V2, comp_mul, ← Category.assoc, ← Category.assoc, quotient_projection_one, quotient_projection_two, Category.id_comp, Category.id_comp]

theorem retraction_one_tangent_sum {v v' : epsAt x ⟶ G} (hv' : IsTanAt G x v') : retractionOne x ≫ V2 x v v' = v := by
  rw [V2, comp_mul, ← Category.assoc, ← Category.assoc, retraction_one_projection_one, retraction_one_projection_two, Category.id_comp, scale0 x hv',
    _root_.mul_one]

theorem retraction_two_tangent_sum {v v' : epsAt x ⟶ G} (hv : IsTanAt G x v) : retractionTwo x ≫ V2 x v v' = v' := by
  rw [V2, comp_mul, ← Category.assoc, ← Category.assoc, retraction_two_projection_one, retraction_two_projection_two, Category.id_comp, scale0 x hv,
    _root_.one_mul]

end Sch

end PositivityTheory.Xgf.TwoTangentVectors
