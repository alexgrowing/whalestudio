import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCochFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusLieAlgebraCoordinateLinearEquiv
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory CartesianMonoidalCategory MonObj Matrix Topology
open Formalism.BasicNotions ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CubeFib GlobalTheory.LieMet GlobalTheory.LieHt GlobalTheory.LocM.Frm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh GlobalTheory.Toroidal GlobalTheory.HeightParts GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.BdFib
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.Pj
open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps (torus lieAdd lieCoord)
open ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs (lieScale)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BdFib

section CochFrame

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X)
  {k : Type} [CommRing k] (x : Sp k ⟶ X)

def fibPush (y : specO k (DualNumber k) ⟶ (Over.pullback x).obj t.G) : overAt x (DualNumber k) ⟶ t.G :=
  pushPt (isGrpPullback_pullback t.G x).1.w y

theorem fibPush_left (y : specO k (DualNumber k) ⟶ (Over.pullback x).obj t.G) :
    (fibPush t x y).left = y.left ≫ pullback.fst t.G.hom x := rfl

theorem fibPush_mul (y y' : specO k (DualNumber k) ⟶ (Over.pullback x).obj t.G) :
    fibPush t x (y * y') = fibPush t x y * fibPush t x y' :=
  map_mul (pushHom (isGrpPullback_pullback t.G x) (specO k (DualNumber k))) y y'

theorem fibPush_one : fibPush t x (1 : specO k (DualNumber k) ⟶ (Over.pullback x).obj t.G) = 1 :=
  map_one (pushHom (isGrpPullback_pullback t.G x) (specO k (DualNumber k)))

theorem smT_fibPush (a : k) (y : specO k (DualNumber k) ⟶ (Over.pullback x).obj t.G) :
    smT x a (fibPush t x y) = fibPush t x (ptMap (dualScale a) ≫ y) :=
  Over.OverMorphism.ext (by
    rw [smT_left, fibPush_left, fibPush_left, Over.comp_left, Category.assoc]
    rfl)

end CochFrame

section TorusLie

variable {R : Type} [CommRing R]

def lieOne (G : Over (Spec (CommRingCat.of R))) [GrpObj G] : LieG G :=
  ⟨1, by rw [MonObj.comp_one, Hom.one_def]⟩

theorem lieCoord_lieOne (r : ℕ) : lieCoord (lieOne (torus R r)) = 0 := by
  have h := (GlobalTheory.TorusLieCoord.lieCoord_bijective_add_smul R r).2.1 (lieOne _) (lieOne _)
  have e : lieAdd _ (lieOne (torus R r)) (lieOne _) = lieOne _ := Subtype.ext (mul_one _)
  rw [e] at h
  simpa using h.symm

theorem lieScale_zero_eq {r : ℕ} (e : LieG (torus R r)) : lieScale _ 0 e = lieOne _ :=
  (GlobalTheory.TorusLieCoord.lieCoord_bijective_add_smul R r).1.1 (by
    rw [(GlobalTheory.TorusLieCoord.lieCoord_bijective_add_smul R r).2.2, zero_smul, lieCoord_lieOne])

end TorusLie

section CochFrame

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X)
  {k : Type} [CommRing k] (x : Sp k ⟶ X) {r : ℕ} (u : torus k r ⟶ (Over.pullback x).obj t.G) [IsMonHom u]

theorem fibPush_tan (e : LieG (torus k r)) : smT x 0 (fibPush t x (e.1 ≫ u)) = 1 := by
  rw [smT_fibPush, ← Category.assoc]
  change fibPush t x ((lieScale _ 0 e).1 ≫ u) = 1
  rw [lieScale_zero_eq]
  change fibPush t x (1 ≫ u) = 1
  rw [MonObj.one_comp, fibPush_one]

def cochMap (e : LieG (torus k r)) : TanM x t.G := mkT (fibPush t x (e.1 ≫ u)) (fibPush_tan t x u e)

theorem cochMap_left (e : LieG (torus k r)) :
    (tv (cochMap t x u e)).left = e.1.left ≫ u.left ≫ pullback.fst t.G.hom x := by
  show (e.1 ≫ u).left ≫ _ = _
  rw [Over.comp_left, Category.assoc]

theorem cochMap_add (e f : LieG (torus k r)) :
    cochMap t x u (lieAdd _ e f) = cochMap t x u e + cochMap t x u f :=
  tanM_ext (by
    show fibPush t x ((e.1 * f.1) ≫ u) = fibPush t x (e.1 ≫ u) * fibPush t x (f.1 ≫ u)
    rw [MonObj.mul_comp, fibPush_mul])

theorem cochMap_smul (a : k) (e : LieG (torus k r)) : cochMap t x u (lieScale _ a e) = a • cochMap t x u e :=
  tanM_ext (by
    show fibPush t x ((ptMap (dualScale a) ≫ e.1) ≫ u) = smT x a (fibPush t x (e.1 ≫ u))
    rw [smT_fibPush, Category.assoc])

theorem cochMap_injective [Mono u.left] : Function.Injective (cochMap t x u) := by
  intro e f h
  have h1 := congrArg (fun v => (tv v).left) h
  simp only [cochMap_left] at h1
  have h2 : e.1.left ≫ u.left = f.1.left ≫ u.left := by
    apply pullback.hom_ext
    · simpa only [Category.assoc] using h1
    · have w : u.left ≫ pullback.snd t.G.hom x = (torus k r).hom := Over.w u
      rw [Category.assoc, Category.assoc, w, Over.w e.1, Over.w f.1]
  exact Subtype.ext (Over.OverMorphism.ext ((cancel_mono u.left).1 h2))

end CochFrame

theorem isCochFrame_linearIndependent : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (k : Type) [Field k] (x : Sp k ⟶ X) (r : ℕ) (ε : Fin r → TanM x t.G), IsCochFrame t x ε → LinearIndependent k ε := by
  intro E _ _ _ H X t k _ x r ε h
  obtain ⟨u, hu, hci, he⟩ := h
  haveI := hu
  haveI : Mono u.left := inferInstance
  obtain ⟨hb, hadd, hsm⟩ := GlobalTheory.TorusLieCoord.lieCoord_bijective_add_smul k r
  let g := (Equiv.ofBijective _ hb).symm
  have hg : ∀ c, lieCoord (g c) = c := fun c => (Equiv.ofBijective _ hb).apply_symm_apply c
  have gadd : ∀ c d, g (c + d) = lieAdd _ (g c) (g d) := fun c d => hb.1 (by
    rw [hadd, hg, hg, hg])
  have gsm : ∀ (a : k) c, g (a • c) = lieScale _ a (g c) := fun a c => hb.1 (by
    rw [hsm, hg, hg])
  let L : (Fin r → k) →ₗ[k] TanM x t.G :=
    { toFun := fun c => cochMap t x u (g c)
      map_add' := fun c d => by rw [gadd, cochMap_add]
      map_smul' := fun a c => by simp only [RingHom.id_apply]; rw [gsm, cochMap_smul] }
  have hL : Function.Injective L := (cochMap_injective t x u).comp (Equiv.ofBijective _ hb).symm.injective
  have hε : ε = L ∘ (Pi.basisFun k (Fin r)) := funext fun i => by
    obtain ⟨e, he1, he2⟩ := he i
    refine tan_ext ?_
    rw [he2]
    show _ = (tv (cochMap t x u (g (Pi.basisFun k (Fin r) i)))).left
    rw [cochMap_left, Pi.basisFun_apply, ← he1]
    simp [g]
  rw [hε]
  exact (Pi.basisFun k (Fin r)).linearIndependent.map' L (LinearMap.ker_eq_bot.2 hL)

end GlobalTheory.BdFib

end
