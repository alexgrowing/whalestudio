import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.GrpTangentPt

variable {S : Scheme.{0}} {R' : Type} [CommRing R'] (x : Sp R' ⟶ S)

def sqZeroMapPt {M N : Type} [AddCommGroup M] [Module R' M] [Module R'ᵐᵒᵖ M] [IsCentralScalar R' M]
    [AddCommGroup N] [Module R' N] [Module R'ᵐᵒᵖ N] [IsCentralScalar R' N] (l : M →ₗ[R'] N) :
    Over.mk (spMap (algebraMap R' (TrivSqZeroExt R' N)) ≫ x) ⟶
      Over.mk (spMap (algebraMap R' (TrivSqZeroExt R' M)) ≫ x) :=
  Over.homMk (spMap (TrivSqZeroExt.map l).toRingHom) (by
    change Spec.map _ ≫ Spec.map _ ≫ x = Spec.map _ ≫ x
    rw [← Category.assoc, ← Spec.map_comp]
    congr 2
    exact CommRingCat.hom_ext (TrivSqZeroExt.map l).comp_algebraMap)

lemma sqZeroMapPt_comp {M N P : Type} [AddCommGroup M] [Module R' M] [Module R'ᵐᵒᵖ M] [IsCentralScalar R' M]
    [AddCommGroup N] [Module R' N] [Module R'ᵐᵒᵖ N] [IsCentralScalar R' N]
    [AddCommGroup P] [Module R' P] [Module R'ᵐᵒᵖ P] [IsCentralScalar R' P]
    (l : M →ₗ[R'] N) (l' : N →ₗ[R'] P) :
    sqZeroMapPt x l' ≫ sqZeroMapPt x l = sqZeroMapPt x (l' ∘ₗ l) := by
  ext1
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun z => ?_)
  ext <;> simp

abbrev epsScalePt (c : R') : epsPtR x ⟶ epsPtR x := sqZeroMapPt x (c • (LinearMap.id : R' →ₗ[R'] R'))

lemma epsScalePt_left (c : R') : (epsScalePt x c).left = spMap (epsScaleR c) := rfl

lemma sqZeroMapPt_comp_eq {M : Type} [AddCommGroup M] [Module R' M] [Module R'ᵐᵒᵖ M]
    [IsCentralScalar R' M] (l : R' →ₗ[R'] M) (l' : M →ₗ[R'] R') :
    sqZeroMapPt x l' ≫ sqZeroMapPt x l = epsScalePt x (l' (l 1)) := by
  rw [sqZeroMapPt_comp]
  congr 1
  refine LinearMap.ext_ring ?_
  simp

lemma epsScalePt_one : epsScalePt x (1 : R') = 𝟙 _ := by
  ext1
  change Spec.map _ = 𝟙 _
  rw [← Spec.map_id]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun z => ?_)
  ext <;> simp

variable {G : Over S} [GrpObj G]

lemma epsScalePt_zero_comp {w : epsPtR x ⟶ G}
    (hw : spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ w.left = (1 : Over.mk x ⟶ G).left) :
    epsScalePt x 0 ≫ w = 1 := by
  let π : epsPtR x ⟶ Over.mk x := Over.homMk (spMap (algebraMap R' (DualNumber R'))) rfl
  have e : (1 : epsPtR x ⟶ G) = π ≫ (1 : Over.mk x ⟶ G) := (comp_one π).symm
  rw [e]
  ext1
  rw [Over.comp_left, Over.comp_left, ← hw, ← Category.assoc]
  congr 1
  change Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun z => ?_)
  ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]

theorem epsScalePt_add_comp (a b : R') {w : epsPtR x ⟶ G}
    (hw : spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ w.left = (1 : Over.mk x ⟶ G).left) :
    epsScalePt x (a + b) ≫ w = (epsScalePt x a ≫ w) * (epsScalePt x b ≫ w) := by
  let i₁ := LinearMap.inl R' R' R'
  let i₂ := LinearMap.inr R' R' R'
  have key : sqZeroMapPt x (i₁ + i₂) ≫ w = (sqZeroMapPt x i₁ ≫ w) * (sqZeroMapPt x i₂ ≫ w) := by
    ext1
    refine GlobalTheory.TangentCrit.hom_ext_of_ker_inf
      (CommRingCat.ofHom (TrivSqZeroExt.map (LinearMap.fst R' R' R')).toRingHom)
      (CommRingCat.ofHom (TrivSqZeroExt.map (LinearMap.snd R' R' R')).toRingHom) ?_ ?_ ?_ ?_
    · refine (PrimeSpectrum.isHomeomorph_comap (TrivSqZeroExt.map (LinearMap.fst R' R' R')).toRingHom
        (fun z => ⟨1, one_pos, TrivSqZeroExt.map i₁ z, by ext <;> simp [i₁]⟩) fun d hd => ?_).surjective
      have h : d.fst = 0 := by simpa using congrArg TrivSqZeroExt.fst hd
      exact ⟨2, by ext1 <;> simp [pow_two, h]⟩
    · intro d h₁ h₂
      have h₃ : d.fst = 0 := by simpa using congrArg TrivSqZeroExt.fst h₁
      have h₄ : d.snd.1 = 0 := by simpa using congrArg TrivSqZeroExt.snd h₁
      have h₅ : d.snd.2 = 0 := by simpa using congrArg TrivSqZeroExt.snd h₂
      exact TrivSqZeroExt.ext h₃ (Prod.ext h₄ h₅)
    · refine congrArg Over.Hom.left
        (?_ : sqZeroMapPt x (LinearMap.fst R' R' R') ≫ _ = sqZeroMapPt x (LinearMap.fst R' R' R') ≫ _)
      rw [comp_mul]
      simp only [← Category.assoc, sqZeroMapPt_comp_eq]
      simp [i₁, i₂, epsScalePt_zero_comp x hw, epsScalePt_one]
    · refine congrArg Over.Hom.left
        (?_ : sqZeroMapPt x (LinearMap.snd R' R' R') ≫ _ = sqZeroMapPt x (LinearMap.snd R' R' R') ≫ _)
      rw [comp_mul]
      simp only [← Category.assoc, sqZeroMapPt_comp_eq]
      simp [i₁, i₂, epsScalePt_zero_comp x hw, epsScalePt_one]
  have := congrArg (sqZeroMapPt x (a • LinearMap.fst R' R' R' + b • LinearMap.snd R' R' R') ≫ ·) key
  simp only [comp_mul, ← Category.assoc, sqZeroMapPt_comp_eq] at this
  simpa [i₁, i₂] using this

theorem tanadd : ∀ {S : Scheme.{0}} (G : Over S) [GrpObj G] {R' : Type} [CommRing R'] (x : Sp R' ⟶ S)
    (w : epsPtR x ⟶ G), spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ w.left = (1 : Over.mk x ⟶ G).left →
    ∀ (a b : R') (wa wb : epsPtR x ⟶ G), wa.left = spMap (epsScaleR a) ≫ w.left →
      wb.left = spMap (epsScaleR b) ≫ w.left → (wa * wb).left = spMap (epsScaleR (a + b)) ≫ w.left := by
  intro S G _ R' _ x w hw a b wa wb ha hb
  have ea : wa = epsScalePt x a ≫ w := Over.OverMorphism.ext ha
  have eb : wb = epsScalePt x b ≫ w := Over.OverMorphism.ext hb
  rw [ea, eb, ← epsScalePt_add_comp x a b hw]
  rfl

end GlobalTheory.GrpTangentPt
