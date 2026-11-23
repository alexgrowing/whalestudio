import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntDerApply
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GermEqZeroOfThickenings
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Heat

theorem isInv_constFn (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G]
    (v : TanM (𝟙 (Sp R)) G) (dd : Fld G.left) (hv : IsInv G v dd) (O : G.left.Opens) (r : R) :
    dd O (constFn G.hom O r) = 0 := by
  refine TopCat.Presheaf.section_ext G.left.sheaf O _ _ fun y hy => ?_
  let g : Sp (G.left.presheaf.stalk y) ⟶ G.left := G.left.fromSpecStalk y
  let φ : R →+* G.left.presheaf.stalk y := (Spec.preimage (g ≫ G.hom)).hom
  have hφ : g ≫ G.hom = spMap φ := (Spec.map_preimage (g ≫ G.hom)).symm
  have ht : ⊤ ≤ g ⁻¹ᵁ O := by
    intro z _
    have hz : g z ∈ Set.range g := ⟨z, rfl⟩
    rw [Scheme.range_fromSpecStalk] at hz
    exact hz.mem_open O.isOpen hy
  have hcomp : ∀ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (f' : B →+* C),
      spMap (f'.comp f) = spMap f' ≫ spMap f := by
    intro A B C _ _ _ f f'
    show Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp]
    rfl
  let g' : tEpsG (g ≫ G.hom) ⟶ G :=
    Over.homMk (spMap (algebraMap _ (DualNumber (G.left.presheaf.stalk y))) ≫ g) (by simp)
  have hdual : (dualMap φ).comp (algebraMap R (DualNumber R)) =
      (algebraMap _ (DualNumber (G.left.presheaf.stalk y))).comp φ := by
    ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  let v' : tEpsG (g ≫ G.hom) ⟶ G :=
    Over.homMk (spMap (dualMap φ) ≫ (tv v).left) (by
      rw [Category.assoc, Over.w (tv v)]
      simp only [Over.mk_hom, Category.comp_id]
      rw [← hcomp, hdual, hcomp, hφ])
  have key := hv.2 _ φ g (g' * v').left O (constFn G.hom O r) hφ ht ⟨g', v', rfl, rfl, rfl⟩
  have h0 : (valR (g' * v').left O (constFn G.hom O r)).snd = 0 := by
    by_cases hw : ⊤ ≤ (g' * v').left ⁻¹ᵁ O
    · rw [GlobalTheory.Points.valR_constFn_of_over G.hom ((algebraMap _ (DualNumber (G.left.presheaf.stalk y))).comp φ)
        _ ?_ O hw r]
      · simp [TrivSqZeroExt.algebraMap_eq_inl]
      · rw [Over.w (g' * v'), hcomp]
        simp only [Over.mk_hom]
        rw [hφ]
    · simp [valR, dif_neg hw]
  rw [h0] at key
  exact ((GlobalTheory.FormalValue.valR_fromSpecStalk y O hy _).symm.trans key.symm).trans
    (map_zero (G.left.presheaf.germ O y hy).hom).symm

end GlobalTheory.Heat
