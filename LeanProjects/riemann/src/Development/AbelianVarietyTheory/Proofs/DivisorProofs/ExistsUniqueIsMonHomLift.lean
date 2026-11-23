import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveCrystalHodgeLiftClasses
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqCompSectionOfProperSmoothNilpotentRigidity

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HomLift

theorem eq_one_of_grpPullback {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [GrpObj G]
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {T : Over S'}
    (z : Over.mk (T.hom ≫ f) ⟶ G) (hz : z.left = (1 : T ⟶ G').left ≫ φ) : z = 1 := by
  have e := h.2 T 1 1 z z hz hz
  rw [_root_.mul_one, ← hz] at e
  exact _root_.mul_eq_left.1 (Over.OverMorphism.ext e)

theorem one_left {S : Scheme.{0}} (T G : Over S) [GrpObj G] :
    (1 : T ⟶ G).left = T.hom ≫ (η[G] : 𝟙_ (Over S) ⟶ G).left := by
  rw [Hom.one_def, Over.comp_left]
  rfl

theorem one_eq_unit {S : Scheme.{0}} (G : Over S) [GrpObj G] :
    (1 : 𝟙_ (Over S) ⟶ G) = η[G] := by
  rw [Hom.one_def, toUnit_unit, Category.id_comp]

theorem existsUnique_isMonHom_lift :
    ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → IsNilpotent (RingHom.ker π) →
    ∀ (A₀ B₀ : Over (Sp R₀)) [GrpObj A₀] [GrpObj B₀] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (i : A₀.left ⟶ A.left) (j : B₀.left ⟶ B.left),
    IsGrpPullback A₀ A (spMap π) i → IsGrpPullback B₀ B (spMap π) j → IsAbelianScheme A → IsAbelianScheme B →
    ∀ (f₀ : A₀ ⟶ B₀) [IsMonHom f₀] (φ : A ⟶ B), i ≫ φ.left = f₀.left ≫ j → ∃! f : A ⟶ B, IsMonHom f ∧ i ≫ f.left = f₀.left ≫ j := by
  intro R R₀ _ _ π hπ hnil A₀ B₀ _ _ A B _ _ i j hA hB hAab hBab f₀ _ φ hφ
  obtain ⟨z, hz⟩ : ∃ z : Over.mk (A₀.hom ≫ spMap π) ⟶ A, z.left = i := ⟨Over.homMk i hA.1.w, rfl⟩
  have hzl : ∀ g : A ⟶ B, (z ≫ g).left = i ≫ g.left := fun g => by rw [Over.comp_left, hz]
  have hu : (1 : A₀ ⟶ A₀).left ≫ i = (1 : Over.mk (A₀.hom ≫ spMap π) ⟶ A).left := by
    have := eq_one_of_grpPullback hA (T := A₀) (Over.homMk ((1 : A₀ ⟶ A₀).left ≫ i) (by
      change (_ ≫ i) ≫ A.hom = A₀.hom ≫ spMap π
      rw [Category.assoc, hA.1.w, ← Category.assoc, Over.w])) rfl
    rw [← this]; rfl
  have h1 : (1 : A₀ ⟶ A₀) ≫ f₀ = 1 := by
    rw [Hom.one_def, Hom.one_def, Category.assoc, IsMonHom.one_hom]
  have hc : z ≫ ((1 : A ⟶ A) ≫ φ) = 1 := by
    apply eq_one_of_grpPullback hB
    rw [← Category.assoc, comp_one, Over.comp_left, ← h1, Over.comp_left, Category.assoc, ← hφ,
      ← Category.assoc, hu]
  obtain ⟨f, hfdef⟩ : ∃ f : A ⟶ B, f = φ * ((1 : A ⟶ A) ≫ φ)⁻¹ := ⟨_, rfl⟩
  have hηf : η[A] ≫ f = η[B] := by
    have e : η[A] ≫ ((1 : A ⟶ A) ≫ φ) = η[A] ≫ φ := by
      rw [← Category.assoc, comp_one, one_eq_unit]
    rw [hfdef, comp_mul, GrpObj.comp_inv, e, mul_inv_cancel, one_eq_unit]
  have hf : IsMonHom f := GlobalTheory.rigidity_holds (Sp R) A B hAab hBab f hηf
  have hfl : i ≫ f.left = f₀.left ≫ j := by
    rw [← hzl, hfdef, comp_mul, GrpObj.comp_inv, hc, inv_one, _root_.mul_one, hzl, hφ]
  refine ⟨f, ⟨hf, hfl⟩, fun g ⟨hg, hgl⟩ => ?_⟩
  obtain ⟨d, hddef⟩ : ∃ d : A ⟶ B, d = g * f⁻¹ := ⟨_, rfl⟩
  have hzg : z ≫ g = z ≫ f := Over.OverMorphism.ext (by rw [hzl, hzl, hgl, hfl])
  have hzd : z ≫ d = 1 := by rw [hddef, comp_mul, GrpObj.comp_inv, hzg, mul_inv_cancel]
  have hηd : η[A] ≫ d = η[B] := by
    rw [hddef, comp_mul, GrpObj.comp_inv, hηf, IsMonHom.one_hom, mul_inv_cancel, one_eq_unit]
  have key := GlobalTheory.Rigidity.eq_comp_section R R₀ π hπ hnil A B A₀ i hA.1 hAab.smooth hAab.proper
    hAab.geomConnected (η[A] : 𝟙_ (Over (Sp R)) ⟶ A).left (Over.w _) d
    (spMap π ≫ (η[B] : 𝟙_ (Over (Sp R)) ⟶ B).left) (by
      rw [← hzl, hzd, one_left]
      exact Category.assoc _ _ _)
  have hd : d = 1 := by
    apply Over.OverMorphism.ext
    rw [key, one_left, ← hηd]
    rfl
  rw [hddef] at hd
  exact mul_inv_eq_one.1 hd

end GlobalTheory.HomLift
