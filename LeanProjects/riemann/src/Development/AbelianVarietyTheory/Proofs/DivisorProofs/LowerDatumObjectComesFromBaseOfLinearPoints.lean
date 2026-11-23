import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratingDegenerationDataPrincipalTripleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalRingLinearHomSchemeLowerObjectStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UCanon

theorem lowBase_of_linearPoints : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D' : Datum H) {l : Geo.Tor.Level H} (c : Coeff l) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (bV : c.F →+* V) (o' : LowObj D' c bV) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X] (x : X → (𝟙_ (Over (Sp V)) ⟶ o'.t.G)), (∀ y z, x (y + z) = x y * x z) → (∀ (a : 𝓞 E) y, x (a • y) = x y ≫ o'.t.act.act a) → ∃ (L : LowBase D' c) (θ₀ : L.W →+* V) (e : X ≃ₗ[𝓞 E] L.D.X) (m : ObjMap o' L.o (spMap θ₀)), IsLocalHom θ₀ ∧ θ₀.comp L.b = bV ∧ ∀ y, (x y).left ≫ m.toSABMap.φ ≫ L.φB = spMap θ₀ ≫ (L.D.c (e y)).left := by
  intro E _ _ _ H D' l c V _ _ _ bV o' X _ _ _ _ x hadd hlin
  obtain ⟨W, _, _, _, b, o, x₀, θ₀, m, hft, hadd₀, hlin₀, hloc, hcomp, hx, ⟨fR, fE⟩, hdim⟩ :=
    GlobalTheory.T.exists_localRing_linearHomScheme_lowerObject D' c V bV o' X x hadd hlin
  haveI : IsProper o.t.G.hom := o.proper
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim W o.t.G
    (ReciprocityTheory.ChartRestriction.G.Geo.Tor.AbelianSchemeGerms.isAbelianScheme_of_proper _ o.t.semi)
  obtain ⟨D, hmod, oa, φB, e, hev, hbi, hgen, hw0, hab, hc⟩ :=
    GlobalTheory.T.exists_generating_degenerationData_principalTriple W o.t o.proper o.ample o.ktriv ⟨g, hg⟩ X x₀ hadd₀ hlin₀
  letI := hmod
  haveI hiso : IsIso φB := hab.1.1.isIso_fst_of_isIso
  refine ⟨⟨W, b, hft, o, D, oa, hev, hbi, hgen, hw0, φB, hab, ?_, ?_, ?_⟩, θ₀, e, m, hloc, hcomp, ?_⟩
  · intro A _ _ f₁ f₂ hf o'' m₁ m₂ z h₁ h₂ hz
    refine fR A f₁ f₂ hf o'' m₁ m₂ (fun y => z (e y)) (fun y => ?_) (fun y => ?_) (fun y => hz (e y))
    · rw [← cancel_mono φB, Category.assoc, Category.assoc, hc y]; exact h₁ (e y)
    · rw [← cancel_mono φB, Category.assoc, Category.assoc, hc y]; exact h₂ (e y)
  · intro k _ f o'' m₁ m₂ z h₁ h₂ hz
    refine fE k f o'' m₁ m₂ (fun y => z (e y)) (fun y => ?_) (fun y => ?_) (fun y => hz (e y))
    · rw [← cancel_mono φB, Category.assoc, Category.assoc, hc y]; exact h₁ (e y)
    · rw [← cancel_mono φB, Category.assoc, Category.assoc, hc y]; exact h₂ (e y)
  · obtain ⟨a, t, h1, h2, h3⟩ := hdim
    exact ⟨a, t, h1, h2, by rw [h3, LinearEquiv.finrank_eq e]⟩
  · intro y
    show (x y).left ≫ m.toSABMap.φ ≫ φB = spMap θ₀ ≫ (D.c (e y)).left
    rw [← hc y, ← Category.assoc, hx y, Category.assoc]

end GlobalTheory.UCanon
