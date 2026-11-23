import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProperGroupSchemePointsValuationRingMulEquivStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
namespace GlobalTheory.LevExt

noncomputable def pullPtsEquiv {S S' : Scheme.{0}} (A : Over S') [GrpObj A] (G : Over S) [GrpObj G] (f : S' ⟶ S)
    (φ : A.left ⟶ G.left) (h : IsGrpPullback A G f φ) (T : Over S') :
    (T ⟶ A) ≃* (Over.mk (T.hom ≫ f) ⟶ G) :=
  MulEquiv.mk' (Equiv.ofBijective
    (fun x => Over.homMk (x.left ≫ φ) (by
      simp only [Over.mk_hom, Category.assoc]
      rw [h.1.w, ← Category.assoc, Over.w]))
    (by
      constructor
      · intro x x' hx
        have hx' : x.left ≫ φ = x'.left ≫ φ := congrArg CommaMorphism.left hx
        ext1
        exact h.1.hom_ext hx' (by rw [Over.w, Over.w])
      · intro z
        refine ⟨Over.homMk (h.1.lift z.left T.hom (by simpa using z.w)) (by simp), ?_⟩
        ext1
        exact h.1.lift_fst _ _ _))
    (by
      intro x y
      ext1
      exact (h.2 T x y (Over.homMk (x.left ≫ φ) (by
          simp only [Over.mk_hom, Category.assoc]
          rw [h.1.w, ← Category.assoc, Over.w])) (Over.homMk (y.left ≫ φ) (by
          simp only [Over.mk_hom, Category.assoc]
          rw [h.1.w, ← Category.assoc, Over.w])) rfl rfl).symm)

@[simp] lemma pullPtsEquiv_left {S S' : Scheme.{0}} (A : Over S') [GrpObj A] (G : Over S) [GrpObj G] (f : S' ⟶ S)
    (φ : A.left ⟶ G.left) (h : IsGrpPullback A G f φ) (T : Over S') (x : T ⟶ A) :
    (pullPtsEquiv A G f φ h T x).left = x.left ≫ φ := rfl

noncomputable def precompEquiv {C : Type*} [Category C] [CartesianMonoidalCategory C] {T₁ T₂ M : C} [GrpObj M]
    (i : T₁ ≅ T₂) : (T₂ ⟶ M) ≃* (T₁ ⟶ M) where
  toFun x := i.hom ≫ x
  invFun x := i.inv ≫ x
  left_inv x := by simp
  right_inv x := by simp
  map_mul' x y := MonObj.comp_mul _ _ _

end GlobalTheory.LevExt

namespace GlobalTheory.LevExt

theorem sections_generic_mulEquiv : ∀ (W L : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] (G : Over (Sp W)) [GrpObj G] (A : Over (Sp L)) [GrpObj A] (φ : A.left ⟶ G.left), IsProper G.hom → IsGrpPullback A G (spMap (algebraMap W L)) φ → ∃ e : (𝟙_ (Over (Sp L)) ⟶ A) ≃* (𝟙_ (Over (Sp W)) ⟶ G), ∀ y, y.left ≫ φ = spMap (algebraMap W L) ≫ (e y).left := by
  intro W L _ _ _ _ _ _ G _ A _ φ hP hφ
  obtain ⟨e1, he1⟩ := GlobalTheory.T.proper_group_scheme_points_valuationRing_mulEquiv W L (Sp W) G hP (𝟙 (Sp W))
  let i : Over.mk (spMap (algebraMap W L) ≫ 𝟙 (Sp W)) ≅ Over.mk ((𝟙_ (Over (Sp L))).hom ≫ spMap (algebraMap W L)) :=
    Over.isoMk (Iso.refl _) (by simp)
  let e : (𝟙_ (Over (Sp L)) ⟶ A) ≃* (𝟙_ (Over (Sp W)) ⟶ G) :=
    ((pullPtsEquiv A G (spMap (algebraMap W L)) φ hφ _).trans (precompEquiv i)).trans e1.symm
  refine ⟨e, fun y => ?_⟩
  have h1 := he1 (e y)
  have h2 : e1 (e y) = i.hom ≫ pullPtsEquiv A G (spMap (algebraMap W L)) φ hφ _ y := e1.apply_symm_apply _
  rw [h2] at h1
  simp only [i] at h1
  simp only [Over.isoMk_hom_left, Iso.refl_hom, Over.comp_left] at h1
  rw [← h1]
  simp only [Category.id_comp]
  rfl

end GlobalTheory.LevExt
