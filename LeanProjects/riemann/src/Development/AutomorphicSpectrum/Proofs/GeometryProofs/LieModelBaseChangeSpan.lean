import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFiniteBaseChange
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFiniteProjectiveBis
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.LieSpan

theorem span_range_pullback : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [Smooth G.hom] (R R' : Type) [CommRing R] [CommRing R'] (c : R →+* R') (x : Spec (CommRingCat.of R) ⟶ S) (E E' : Type) [AddCommGroup E] [Module R E] [AddCommGroup E'] [Module R' E'] (M : LieModel G x E) (M' : LieModel G (Spec.map (CommRingCat.ofHom c) ≫ x) E') (j : E → E'), (∀ e, (M'.pt (j e)).left = Spec.map (CommRingCat.ofHom (dualMap c)) ≫ (M.pt e).left) → Submodule.span R' (Set.range j) = ⊤ := by
  intro S G _ _ R R' _ _ c x E E' _ _ _ _ M M' j hj
  letI : Algebra R R' := c.toAlgebra
  letI : Module R E' := Module.compHom E' c
  haveI : IsScalarTower R R' E' :=
    ⟨fun r r' e => by
      show (c r * r') • e = c r • (r' • e)
      exact mul_smul _ _ _⟩
  let h : GlobalTheory.CompanionTheory.Ar.epsAt (Spec.map (CommRingCat.ofHom c) ≫ x) ⟶ GlobalTheory.CompanionTheory.Ar.epsAt x :=
    Over.homMk (Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap c))) (by
      show Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap c)) ≫
          Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) ≫ x =
        Spec.map (CommRingCat.ofHom (algebraMap R' (DualNumber R'))) ≫
          Spec.map (CommRingCat.ofHom c) ≫ x
      rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
      congr 2
      ext r <;> simp [GlobalTheory.CompanionTheory.Ar.dualMap, TrivSqZeroExt.algebraMap_eq_inl, CommRingCat.hom_comp,
        CommRingCat.hom_ofHom])
  have hl : h.left = Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap c)) := rfl
  have hpt : ∀ e, M'.pt (j e) = h ≫ M.pt e := fun e =>
    Over.OverMorphism.ext (by rw [Over.comp_left, hl]; exact hj e)
  have hadd : ∀ a b, j (a + b) = j a + j b := by
    intro a b
    apply M'.inj
    rw [M'.add, hpt, hpt, hpt, M.add, MonObj.comp_mul]
  have hsmul : ∀ (r : R) (e : E), j (r • e) = c r • j e := by
    intro r e
    apply M'.inj
    apply Over.OverMorphism.ext
    rw [M'.smul, hpt, hpt, Over.comp_left, Over.comp_left, M.smul, hl,
      ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
    congr 2
    ext a <;>
      simp [GlobalTheory.CompanionTheory.Ar.dualMap, GlobalTheory.CompanionTheory.Ar.epsMul, smul_eq_mul, TrivSqZeroExt.algebraMap_eq_inl, CommRingCat.hom_comp,
        CommRingCat.hom_ofHom]
  let β : E →ₗ[R] E' :=
    { toFun := j, map_add' := hadd, map_smul' := fun r e => hsmul r e }
  obtain ⟨-, -, hbc⟩ := GlobalTheory.CompanionTheory.Ar.LieProj.lie_finite_projective_baseChange S G R x E M
  have hb : IsBaseChange R' β := hbc R' E' M' β (fun e => hj e)
  rw [eq_top_iff]
  rintro y -
  obtain ⟨t, rfl⟩ := hb.equiv.surjective y
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul s e =>
    rw [hb.equiv_tmul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨e, rfl⟩)
  | add a b ha hb' =>
    rw [map_add]
    exact Submodule.add_mem _ ha hb'

end GlobalTheory.CompanionTheory.Ar.LieSpan
