import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
import ReciprocityTheory.DualLattices.TowerZeroSurjective
import ReciprocityTheory.DualLattices.LinPairStatement
import ReciprocityTheory.DualLattices.LengthDegreeAbelianVariety
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff

set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.ChF

private theorem mul_left_fst {S S' Z : Scheme.{0}} (G : Over S) [GrpObj G] (f : S' ⟶ S) {t : Z ⟶ S'} {r : Z ⟶ S}
    (x y : Over.mk t ⟶ (Over.pullback f).obj G) (x₀ y₀ : Over.mk r ⟶ G)
    (hx : x₀.left = x.left ≫ pullback.fst G.hom f) (hy : y₀.left = y.left ≫ pullback.fst G.hom f) :
    (x₀ * y₀).left = (x * y).left ≫ pullback.fst G.hom f := by
  have A : ∀ {X Y : Over S} (a : X ⟶ Y),
      ((Over.pullback f).map a).left ≫ pullback.fst Y.hom f = pullback.fst X.hom f ≫ a.left :=
    fun a => pullback.lift_fst _ _ _
  let z : Over.mk t ⟶ (Over.pullback f).obj (G ⊗ G) :=
    lift x y ≫ Functor.LaxMonoidal.μ (Over.pullback f) G G
  have z₁ : z ≫ (Over.pullback f).map (fst G G) = x := by simp [z]
  have z₂ : z ≫ (Over.pullback f).map (snd G G) = y := by simp [z]
  have hz : (lift x₀ y₀).left = z.left ≫ pullback.fst (G ⊗ G).hom f := by
    apply pullback.hom_ext
    · show (lift x₀ y₀ ≫ fst G G).left = _ ≫ (fst G G).left
      rw [lift_fst, hx, Category.assoc, ← A, ← Category.assoc, ← Over.comp_left, z₁]
    · show (lift x₀ y₀ ≫ snd G G).left = _ ≫ (snd G G).left
      rw [lift_snd, hy, Category.assoc, ← A, ← Category.assoc, ← Over.comp_left, z₂]
  have hxy : x * y = z ≫ (Over.pullback f).map μ[G] := by
    rw [Hom.mul_def, Functor.obj.μ_def, ← Category.assoc]
  rw [hxy, Over.comp_left, Category.assoc, A, ← Category.assoc, ← hz]
  rfl

private theorem mono_thick (R : Type) [CommRing R] (I : Ideal R) (k : ℕ) : Mono (Out.thick R I k) := by
  have : IsClosedImmersion (Out.thick R I k) := IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  infer_instance

theorem qRel_existsUnique_mul_nat : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : Out.DegPre R) (k : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (c : Out.GtCoord I D k G), (∀ (S : Type) [CommRing S] [Algebra R S], Kills I k S → (∀ z, ∃! y, QRel c S z y) ∧ ∀ z z' y y', QRel c S z y → QRel c S z' y' → QRel c S (z * z') (y * y')) ∧ ∀ (S : Type) [CommRing S] [Algebra R S] (S' : Type) [CommRing S'] [Algebra R S'] (φ : S →ₐ[R] S') z y, QRel c S z y → QRel c S' (spMap φ ≫ z) (spMap φ ≫ y) := by
  intro R _ _ I D k G _ _ c
  have hm := mono_thick R I k
  have hf : Mono (pullback.fst G.hom (Out.thick R I k)) := inferInstance
  refine ⟨fun S _ _ hS => ?_, ?_⟩
  · let t : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (R ⧸ I ^ (k + 1))) :=
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift (I ^ (k + 1)) (algebraMap R S) hS))
    have ht : t ≫ Out.thick R I k = Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      rfl
    have hw : ∀ (z : sp (R₀ := R) S ⟶ G) (w : Spec (CommRingCat.of S) ⟶ (Out.thickObj R I k G).left),
        w ≫ (Out.fstG I k G).left = z.left → w ≫ (Out.thickObj R I k G).hom = t := by
      intro z w h
      rw [← cancel_mono (Out.thick R I k), ht]
      have h1 : (Out.thickObj R I k G).hom ≫ Out.thick R I k = (Out.fstG I k G).left ≫ G.hom :=
        (pullback.condition (f := G.hom) (g := Out.thick R I k)).symm
      rw [Category.assoc, h1, ← Category.assoc, h]
      exact Over.w z
    refine ⟨fun z => ?_, ?_⟩
    · let w : Spec (CommRingCat.of S) ⟶ (Out.thickObj R I k G).left :=
        pullback.lift z.left t ((Over.w z).trans ht.symm)
      have h1 : w ≫ (Out.fstG I k G).left = z.left := pullback.lift_fst _ _ _
      have h2 : (w ≫ c.pG.left) ≫ D.P.A.hom = Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
        have h3 : c.pG.left ≫ D.P.A.hom = (Out.thickObj R I k G).hom ≫ Out.thick R I k := Over.w c.pG
        rw [Category.assoc, h3, ← Category.assoc, hw z w h1, ht]
      refine ⟨Over.homMk (w ≫ c.pG.left) h2, ⟨w, h1, rfl⟩, ?_⟩
      rintro y ⟨w', a, b⟩
      have e : w' = w := (cancel_mono (pullback.fst G.hom (Out.thick R I k))).1 (a.trans h1.symm)
      apply Over.OverMorphism.ext
      rw [← b, e]
      rfl
    · rintro z z' y y' ⟨w, a, b⟩ ⟨w', a', b'⟩
      have := c.q_hom
      let x : Over.mk t ⟶ Out.thickObj R I k G := Over.homMk w (hw z w a)
      let x' : Over.mk t ⟶ Out.thickObj R I k G := Over.homMk w' (hw z' w' a')
      refine ⟨(x * x').left, (mul_left_fst G (Out.thick R I k) x x' z z' a.symm a'.symm).symm, ?_⟩
      have e := mul_left_fst D.P.A (Out.thick R I k) (x ≫ c.q) (x' ≫ c.q) y y'
        (b.symm.trans (Category.assoc _ _ _).symm) (b'.symm.trans (Category.assoc _ _ _).symm)
      rw [← MonObj.mul_comp] at e
      exact ((Category.assoc _ _ _).symm.trans e.symm)
  · rintro S _ _ S' _ _ φ z y ⟨w, a, b⟩
    refine ⟨(spMap φ).left ≫ w, ?_, ?_⟩
    · exact (Category.assoc _ _ _).trans (congrArg ((spMap φ).left ≫ ·) a)
    · exact (Category.assoc _ _ _).trans (congrArg ((spMap φ).left ≫ ·) b)

end GlobalTheory.ChF
