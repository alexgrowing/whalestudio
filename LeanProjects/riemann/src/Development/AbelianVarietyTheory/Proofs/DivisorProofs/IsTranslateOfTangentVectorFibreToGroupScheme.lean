import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsChartPtChartPt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineHomOfField
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
open GlobalTheory.CechKS

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechKS

section

open MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

theorem exists_mul_of_isGrpPullback {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G]
    {f : S' ⟶ S} {m : G'.left ⟶ G.left} (hm : IsGrpPullback G' G f m) (T : Over S') (x y : T ⟶ G')
    (s : T.left ⟶ S) (hs : s = T.hom ≫ f) :
    ∃ x₀ y₀ : Over.mk s ⟶ G, x₀.left = x.left ≫ m ∧ y₀.left = y.left ≫ m ∧ (x₀ * y₀).left = (x * y).left ≫ m := by
  subst hs
  have e : ∀ z : T ⟶ G', (z.left ≫ m) ≫ G.hom = T.hom ≫ f := fun z ↦ by
    rw [Category.assoc, hm.1.w, ← Category.assoc, Over.w z]
  exact ⟨Over.homMk (x.left ≫ m) (e x), Over.homMk (y.left ≫ m) (e y), rfl, rfl, hm.2 T x y _ _ rfl rfl⟩

end

theorem IsTransl.isTranslate_comp : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X) {K : Type} [Field K] (x0 : Sp K ⟶ X) (A : Over (Sp K)) [GrpObj A] (m : A.left ⟶ t.G.left) (hm : IsGrpPullback A t.G x0 m) {R : Type} [CommRing R] (ψ : R →+* K) (v : Sp (DualNumber R) ⟶ t.G.left) (u : epsR K ⟶ A) (hu : u.left ≫ m = spMap (dualMap ψ) ≫ v) {B : Type} [CommRing B] (φ : K →+* B) (x : Sp B ⟶ A.left) (hx : x ≫ A.hom = spMap φ) (w : Sp (DualNumber B) ⟶ A.left) (hw : IsTransl φ x u w), LogKS.IsTranslate t (φ.comp ψ) (x ≫ m) v (w ≫ m) := by
  intro E _ _ _ H X t K _ x0 A _ m hm R _ ψ v u hu B _ φ x hx w hw
  obtain ⟨x₁, v₁, a, b, rfl⟩ := hw
  have sc : ∀ {P Q T : Type} [CommRing P] [CommRing Q] [CommRing T] (f : P →+* Q) (g : Q →+* T),
      spMap g ≫ spMap f = spMap (g.comp f) := fun f g ↦ by
    unfold spMap
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have dc : (dualMap φ).comp (dualMap ψ) = dualMap (φ.comp ψ) :=
    RingHom.ext fun c ↦ by ext <;> simp [dualMap]
  obtain ⟨x₀, y₀, h₁, h₂, h₃⟩ := exists_mul_of_isGrpPullback hm _ x₁ v₁
    (spMap (algebraMap B (DualNumber B)) ≫ (x ≫ m) ≫ t.G.hom) (by
      change _ = spMap ((algebraMap B (DualNumber B)).comp φ) ≫ x0
      rw [Category.assoc, hm.1.w, ← Category.assoc x, hx, ← Category.assoc, sc])
  refine ⟨x₀, y₀, ?_, ?_, h₃⟩
  · rw [h₁, a]; exact Category.assoc _ _ _
  · rw [h₂, b, ← dc, ← sc (dualMap ψ) (dualMap φ)]
    refine (Category.assoc _ _ _).trans ?_
    rw [hu]; exact (Category.assoc (spMap (dualMap φ)) (spMap (dualMap ψ)) v).symm

end GlobalTheory.CechKS
