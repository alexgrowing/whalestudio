import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntDerApply
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Heat

theorem scheme_constantSection_add {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) (U : X.Opens) (a b : R) :
    constFn p U (a + b) = constFn p U a + constFn p U b := by
  simp [constFn, map_add]

theorem constFn_mul_on_open {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) (U : X.Opens) (a b : R) :
    constFn p U (a * b) = constFn p U a * constFn p U b := by
  simp [constFn, map_mul]

theorem gammaSpecIso_appLE_of_eq_id_apply {R : Type} [CommRing R] (f : Sp R ⟶ Sp R) (hf : f = 𝟙 _) (e : (⊤ : (Sp R).Opens) ≤ f ⁻¹ᵁ ⊤) (r : R) :
    (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom ((f.appLE ⊤ ⊤ e).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) = r := by
  subst hf
  simp only [Scheme.Hom.appLE]
  erw [show (homOfLE e) = 𝟙 _ from Subsingleton.elim _ _]
  simp

theorem gammaSpecIso_appLE_section_constantSection_eq {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) (e : Sp R ⟶ X) (he : e ≫ p = 𝟙 _)
    (U : X.Opens) (h : ⊤ ≤ e ⁻¹ᵁ U) (r : R) :
    (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom ((e.appLE U ⊤ h).hom (constFn p U r)) = r := by
  have hc := Scheme.Hom.appLE_comp_appLE e p ⊤ U ⊤ (fun _ _ => trivial) h
  calc (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom ((e.appLE U ⊤ h).hom (constFn p U r))
      = (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom ((p.appLE ⊤ U (fun _ _ => trivial) ≫ e.appLE U ⊤ h).hom
          ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) := rfl
    _ = _ := by rw [hc]
    _ = r := gammaSpecIso_appLE_of_eq_id_apply _ he _ r

end GlobalTheory.Heat

namespace GlobalTheory.Heat

theorem liftDer_isDerivation : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] (D : R → R) (W : G.left.Opens)
    (d : Fld G.left), IsLift G D W d → ⊤ ≤ (η[G]).left ⁻¹ᵁ W → ∃ D' : Derivation ℤ R R, ∀ r, D' r = D r := by
  intro R _ G _ D W d hL hW
  have he : (η[G]).left ≫ G.hom = 𝟙 _ := by simpa using Over.w (η[G])
  let ev : Γ(G.left, W) →+* R :=
    (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.comp (((η[G]).left.appLE W ⊤ hW).hom)
  have hev : ∀ r, ev (constFn G.hom W r) = r := fun r => gammaSpecIso_appLE_section_constantSection_eq G.hom _ he W hW r
  have hc : ∀ r, d W (constFn G.hom W r) = constFn G.hom W (D r) := hL.2 W le_rfl
  have hadd : ∀ a b, D (a + b) = D a + D b := by
    intro a b
    have := congrArg ev (hc (a + b))
    rw [scheme_constantSection_add, hL.1.1 W le_rfl, hc, hc, map_add, hev, hev, hev] at this
    exact this.symm
  have hmul : ∀ a b, D (a * b) = a * D b + b * D a := by
    intro a b
    have := congrArg ev (hc (a * b))
    rw [constFn_mul_on_open, hL.1.2.1 W le_rfl, hc, hc, map_add, map_mul, map_mul, hev, hev, hev, hev, hev] at this
    exact this.symm
  let L : R →ₗ[ℤ] R := (AddMonoidHom.mk' D hadd).toIntLinearMap
  exact ⟨Derivation.mk' L (fun a b => by simpa [L, smul_eq_mul] using hmul a b), fun r => rfl⟩

end GlobalTheory.Heat
