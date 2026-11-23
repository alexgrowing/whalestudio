import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionRationalOverFiniteExt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushEquivSymmLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteAndFlatTorsion
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.TwoTorsPull

theorem twoTorsRat_of_pullback : ∀ (R : Type) [CommRing R] [IsDomain R] (G : Over (Sp R)) [GrpObj G] (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → ∃ (K' : Type) (_ : Field K') (_ : Algebra (FractionRing R) K'), Module.Finite (FractionRing R) K' ∧ ∀ (R₂ : Type) [CommRing R₂] [IsDomain R₂] (ρ : R →+* R₂) (i : K' →+* FractionRing R₂), (∀ r : R, i (algebraMap (FractionRing R) K' (algebraMap R (FractionRing R) r)) = algebraMap R₂ (FractionRing R₂) (ρ r)) → ∀ (G₁ : Over (Sp R₂)) [GrpObj G₁] (β : G₁.left ⟶ G.left), IsGrpPullback G₁ G (spMap ρ) β → TwoTorsRat G₁ := by
  intro R _ _ G _ A gen hgen
  obtain ⟨K', _, _, hfin, H⟩ := TorsRational.exists_ext_points (FractionRing R) (torsion A.A 2)
    (AbTorsionAnyBase.isFinite_and_flat_torsion _ A.A A.isAb 2 (by norm_num)).1
  refine ⟨K', inferInstance, inferInstance, hfin, ?_⟩
  intro R₂ _ _ ρ i hi G₁ _ β hβ F _ _ x hx
  let f : FractionRing R →+* FractionRing R₂ := i.comp (algebraMap (FractionRing R) K')
  letI : Algebra K' (FractionRing R₂) := i.toAlgebra
  letI : Algebra (FractionRing R) (FractionRing R₂) := f.toAlgebra
  haveI : IsScalarTower (FractionRing R) K' (FractionRing R₂) := IsScalarTower.of_algebraMap_eq' rfl
  let σ : FractionRing R₂ →+* F := algebraMap (FractionRing R₂) F
  have hsq : spMap f ≫ jK R = jK R₂ ≫ spMap ρ := by
    rw [jK, jK, spMap, spMap, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext r
    exact hi r
  have hx2 : x ^ 2 = 1 := by rw [pow_two, hx]

  let x0 := ObjPull.pushEquiv hβ _ x
  have hx0 : x0 ^ 2 = 1 := by simp only [x0, ← map_pow, hx2, map_one]
  have hx0l : x0.left = x.left ≫ β := rfl

  let T : Over (Sp (FractionRing R)) := Over.mk (spMap σ ≫ spMap f)
  have hT : T.hom ≫ jK R = (Over.mk (spMap σ ≫ jK R₂)).hom ≫ spMap ρ := by
    show (spMap σ ≫ spMap f) ≫ jK R = (spMap σ ≫ jK R₂) ≫ spMap ρ
    rw [Category.assoc, hsq, Category.assoc]
  let e : Over.mk (T.hom ≫ jK R) ⟶ Over.mk ((Over.mk (spMap σ ≫ jK R₂)).hom ≫ spMap ρ) :=
    Over.homMk (𝟙 _) (by simpa using hT.symm)
  let x1 := preHom e x0
  have hx1 : x1 ^ 2 = 1 := by rw [← map_pow, hx0, map_one]
  have hx1l : x1.left = x0.left := by
    show (e ≫ x0).left = _
    rw [Over.comp_left]
    exact Category.id_comp _
  let hpb := isGrpPullback_pullback G (jK R)
  let x2 := (ObjPull.pushEquiv hpb T).symm x1
  have hx2' : x2 ^ 2 = 1 := by simp only [x2, ← map_pow, hx1, map_one]
  have hx2l : x2.left ≫ pullback.fst G.hom (jK R) = x1.left := ObjPull.pushEquiv_symm_left hpb T x1
  let x3 := x2 ≫ gen.hom
  have hx3 : x3 ^ 2 = 1 := by
    simp only [x3, pow_two] at hx2' ⊢
    rw [← MonObj.mul_comp, hx2', MonObj.one_comp]
  have hmul : x3 ≫ mulN A.A 2 = toUnit _ ≫ η := by
    rw [GrpTangent.mulN_eq_pow, MonObj.comp_pow, Category.comp_id, hx3, Hom.one_def]
  let t0 : T ⟶ torsion A.A 2 := pullback.lift x3 (toUnit _) hmul
  have ht0 : t0 ≫ torsion.ι A.A 2 = x3 := pullback.lift_fst _ _ _
  have hs : T.hom = spMap (σ.comp (algebraMap (FractionRing R) (FractionRing R₂))) := by
    show spMap σ ≫ spMap f = _
    rw [spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  obtain ⟨w, hw⟩ := H (FractionRing R₂) F σ t0.left ((Over.w t0).trans hs)
  have hw2 : w ≫ (torsion A.A 2).hom = spMap f := by
    refine spec_map_field_cancel σ _ _ ?_
    rw [← Category.assoc, hw, Over.w t0]
    rfl
  let z : Sp (FractionRing R₂) ⟶ G.left := w ≫ (torsion.ι A.A 2).left ≫ gen.inv.left ≫ pullback.fst G.hom (jK R)
  have hz : z ≫ G.hom = jK R₂ ≫ spMap ρ := by
    simp only [z, Category.assoc]
    have hgi : gen.inv.left ≫ pullback.snd G.hom (jK R) = A.A.hom := Over.w gen.inv
    rw [pullback.condition, ← Category.assoc gen.inv.left, hgi, ← Category.assoc (torsion.ι A.A 2).left,
      Over.w (torsion.ι A.A 2), ← Category.assoc w, hw2, hsq]
  let y : Over.mk (jK R₂) ⟶ G₁ := Over.homMk (hβ.1.lift z (jK R₂) hz) (hβ.1.lift_snd _ _ _)
  refine ⟨y, hβ.1.hom_ext ?_ ?_⟩
  · show x.left ≫ β = spMap σ ≫ hβ.1.lift z (jK R₂) hz ≫ β
    rw [hβ.1.lift_fst, ← hx0l, ← hx1l, ← hx2l]
    have hgh : gen.hom.left ≫ gen.inv.left = 𝟙 _ := by rw [← Over.comp_left, Iso.hom_inv_id, Over.id_left]
    simp only [z, ← Category.assoc]
    rw [hw, ← Over.comp_left, ht0]
    show x2.left ≫ pullback.fst G.hom (jK R) = ((x2.left ≫ gen.hom.left) ≫ gen.inv.left) ≫ pullback.fst G.hom (jK R)
    rw [Category.assoc x2.left, hgh, Category.comp_id]
  · show x.left ≫ G₁.hom = spMap σ ≫ hβ.1.lift z (jK R₂) hz ≫ G₁.hom
    rw [hβ.1.lift_snd]
    exact Over.w x

end GlobalTheory.TwoTorsPull
