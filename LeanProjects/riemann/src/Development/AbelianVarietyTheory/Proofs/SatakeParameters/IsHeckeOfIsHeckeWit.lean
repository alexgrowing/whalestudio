import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsHeckeMapLevRefl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassifyingMapSymplecticLevelEquivariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectPullbackBis

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo

namespace GlobalTheory.DrinLev.HT.HeckePt

section Pull

variable {S S' : Scheme.{0}} {f : S' ⟶ S}

theorem ext_of_left {B : Over S} {B' : Over S'} [GrpObj B] [GrpObj B'] {b : B'.left ⟶ B.left}
    (hb : IsGrpPullback B' B f b) {T : Over S'} {u v : T ⟶ B'} (h : u.left ≫ b = v.left ≫ b) : u = v := Over.OverMorphism.ext (hb.1.hom_ext h (by rw [Over.w u, Over.w v]))

variable {A B : Over S} {A' B' : Over S'} [GrpObj A] [GrpObj B] [GrpObj A'] [GrpObj B']
  {a : A'.left ⟶ A.left} {b : B'.left ⟶ B.left}

def pullMor (ha : IsGrpPullback A' A f a) (hb : IsGrpPullback B' B f b) (ψ : A ⟶ B) : A' ⟶ B' :=
  Over.homMk (hb.1.lift (a ≫ ψ.left) A'.hom (by rw [Category.assoc, Over.w ψ, ha.1.w])) (hb.1.lift_snd _ _ _)

theorem pullMor_left (ha : IsGrpPullback A' A f a) (hb : IsGrpPullback B' B f b) (ψ : A ⟶ B) :
    (pullMor ha hb ψ).left ≫ b = a ≫ ψ.left := by
  simp only [pullMor, Over.homMk_left]
  exact hb.1.lift_fst _ _ _

private theorem pushHom_left_satake_parameters {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {φ : G'.left ⟶ G.left}
    (h : IsGrpPullback G' G f φ) (T : Over S') (x : T ⟶ G') : (pushHom h T x).left = x.left ≫ φ := by
  rfl

theorem push_pullMor (ha : IsGrpPullback A' A f a) (hb : IsGrpPullback B' B f b) (ψ : A ⟶ B) (T : Over S')
    (x : T ⟶ A') : pushHom hb T (x ≫ pullMor ha hb ψ) = pushHom ha T x ≫ ψ := by
  apply Over.OverMorphism.ext
  simp only [Over.comp_left, pushHom_left_satake_parameters, Category.assoc, pullMor_left]

private theorem isMonHom_of_comp_mul {C : Type*} [Category C] [CartesianMonoidalCategory C] {G H : C} [GrpObj G] [GrpObj H]
    (g : G ⟶ H) (hg : ∀ (T : C) (x y : T ⟶ G), (x * y) ≫ g = x ≫ g * y ≫ g) : IsMonHom g := by
  constructor
  · have h1 := hg (𝟙_ C) 1 1
    rw [_root_.mul_one] at h1
    have h2 : (1 : 𝟙_ C ⟶ G) ≫ g = 1 := mul_left_cancel (h1.symm.trans (_root_.mul_one _).symm)
    simpa [Hom.one_def, toUnit_unit] using h2
  · have h := hg _ (fst G G) (snd G G)
    simp only [Hom.mul_def, lift_fst_snd, Category.id_comp] at h
    rw [h]
    congr 1
    ext <;> simp

theorem isMonHom_pullMor (ha : IsGrpPullback A' A f a) (hb : IsGrpPullback B' B f b) (ψ : A ⟶ B) [IsMonHom ψ] :
    IsMonHom (pullMor ha hb ψ) := by
  refine isMonHom_of_comp_mul _ fun T x y => ext_of_left hb ?_
  rw [← pushHom_left_satake_parameters hb, ← pushHom_left_satake_parameters hb, push_pullMor, map_mul, map_mul, push_pullMor, push_pullMor,
    MonObj.mul_comp]

theorem pow_id_left (ha : IsGrpPullback A' A f a) (n : ℕ) : ((𝟙 A') ^ n).left ≫ a = a ≫ ((𝟙 A) ^ n).left := by
  have h1 := pushHom_left_satake_parameters ha A' ((𝟙 A') ^ n)
  rw [map_pow] at h1
  rw [← h1]
  have h2 : pushHom ha A' (𝟙 A') ^ n = pushHom ha A' (𝟙 A') ≫ (𝟙 A) ^ n := by
    rw [MonObj.comp_pow, Category.comp_id]
  rw [h2]
  simp only [Over.comp_left, pushHom_left_satake_parameters, Over.id_left, Category.id_comp]

theorem pullMor_comp_eq_pow (ha : IsGrpPullback A' A f a) (hb : IsGrpPullback B' B f b) (ψ : A ⟶ B) (ψ' : B ⟶ A)
    (n : ℕ) (h : ψ ≫ ψ' = (𝟙 A) ^ n) : pullMor ha hb ψ ≫ pullMor hb ha ψ' = (𝟙 A') ^ n := by
  apply ext_of_left ha
  rw [Over.comp_left, Category.assoc, pullMor_left hb ha ψ', ← Category.assoc, pullMor_left ha hb ψ, Category.assoc,
    ← Over.comp_left, h, pow_id_left ha n]

end Pull

end GlobalTheory.DrinLev.HT.HeckePt
