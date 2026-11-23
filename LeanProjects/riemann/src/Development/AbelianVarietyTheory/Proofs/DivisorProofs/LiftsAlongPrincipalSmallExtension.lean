import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.Definitions.Divisors.NotIsIsoSpMapDnFst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftsAlong
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveLineBundleFamilyCalculusRules
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualOpen

theorem liftsAlong_span_singleton : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (U : Over (Sp R)) (M : LB (A ⊗ U).left), Fam A M → SmallLift A M → ∀ (B : Type) [CommRing B] [IsLocalRing B] (t : B), t ∈ IsLocalRing.maximalIdeal B → IsLocalRing.maximalIdeal B * Ideal.span {t} = ⊥ → LiftsAlong A M B (Ideal.span {t}) := by
  intro R _ A _ U M hM hSL B _ _ t ht hmt T N hN y u₀ h₀
  have calc5 := ((GlobalTheory.FamCalc.famCalc (Sp R) A).2.2.2.2)
  have hkill : ∀ a ∈ IsLocalRing.maximalIdeal B, a * t = 0 := fun a ha ↦ by
    have : a * t ∈ IsLocalRing.maximalIdeal B * Ideal.span {t} :=
      Ideal.mul_mem_mul ha (Ideal.mem_span_singleton_self t)
    rwa [hmt, Ideal.mem_bot] at this
  let Y : Over (Sp R) := Over.mk (y ≫ T.hom)
  let yy : Y ⟶ T := Over.homMk y rfl
  have hN' : Fam A (ev N (fst A Y) (snd A Y ≫ yy)) := (GlobalTheory.FamCalc.famCalc (Sp R) A).1 T Y N yy hN
  have key : ptMap (y ≫ T.hom) (Ideal.Quotient.mk (Ideal.span {t})) ≫ yy =
      (Over.homMk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {t}))) ≫ y) (by simp) :
        Over.mk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {t}))) ≫ y ≫ T.hom) ⟶ T) := by
    ext1; rfl
  have h₁ : Same A (ev N (fst A Y) (snd A Y ≫ yy)) M (ptMap (y ≫ T.hom) (Ideal.Quotient.mk (Ideal.span {t}))) u₀ := by
    rw [calc5 T U Y _ N M yy _ u₀ hN.isLB hM.isLB, key]
    exact h₀
  obtain ⟨u, hu⟩ := hSL B t ht hkill (y ≫ T.hom) _ hN' u₀ h₁
  refine ⟨u, ?_⟩
  have := (calc5 T U Y Y N M yy (𝟙 _) u hN.isLB hM.isLB).1 hu
  rwa [Category.id_comp] at this

end GlobalTheory.DualOpen
