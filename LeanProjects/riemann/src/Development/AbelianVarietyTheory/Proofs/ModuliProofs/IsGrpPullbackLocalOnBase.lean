import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.GrpLoc

theorem hom_ext_loc {X Y : Scheme.{0}} {f g : X ⟶ Y}
    (h : ∀ p : X, ∃ (W : Scheme.{0}) (a : W ⟶ X), IsOpenImmersion a ∧ p ∈ Set.range a ∧ a ≫ f = a ≫ g) : f = g := by
  choose W a ha hp hfg using h
  exact Scheme.Cover.hom_ext (Scheme.Cover.mkOfCovers (P := @IsOpenImmersion) X W a
    (fun x => by obtain ⟨y, hy⟩ := hp x; exact ⟨x, y, hy⟩) ha) f g hfg

theorem range_of_isPullback {P X Y Z : Scheme.{0}} {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback a b f g) (x : X) : x ∈ Set.range a ↔ f x ∈ Set.range g := by
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨b p, by rw [← Scheme.Hom.comp_apply, ← h.w, Scheme.Hom.comp_apply]⟩
  · rintro ⟨y, hy⟩
    obtain ⟨q, hq₁, -⟩ := Scheme.Pullback.exists_preimage_pullback x y hy.symm
    refine ⟨h.isoPullback.inv q, ?_⟩
    rw [← Scheme.Hom.comp_apply, h.isoPullback_inv_fst, hq₁]

theorem mul_left_pre {S : Scheme.{0}} {G : Over S} [GrpObj G] {T T' : Over S} (k : T'.left ⟶ T.left)
    (hk : k ≫ T.hom = T'.hom) (x y : T ⟶ G) (x' y' : T' ⟶ G) (hx : x'.left = k ≫ x.left)
    (hy : y'.left = k ≫ y.left) : (x' * y').left = k ≫ (x * y).left := by
  have ex : x' = Over.homMk k hk ≫ x := by ext; simp [hx]
  have ey : y' = Over.homMk k hk ≫ y := by ext; simp [hy]
  rw [ex, ey, ← MonObj.comp_mul, Over.comp_left]
  rfl

theorem isGrpPullback_id_of_loc {S : Scheme.{0}} {A A' : Over S} [GrpObj A] [GrpObj A'] (φ : A.left ⟶ A'.left) [IsIso φ]
    (w : φ ≫ A'.hom = A.hom)
    (h : ∀ p : S, ∃ (W : Scheme.{0}) (x : W ⟶ S) (B : Over W) (_ : GrpObj B) (a : B.left ⟶ A.left),
      IsOpenImmersion x ∧ p ∈ Set.range x ∧ IsGrpPullback B A x a ∧ IsGrpPullback B A' x (a ≫ φ)) :
    IsGrpPullback A A' (𝟙 S) φ := by
  refine ⟨IsPullback.of_horiz_isIso ⟨by simpa using w⟩, ?_⟩
  intro T x y x₀ y₀ hx hy
  apply hom_ext_loc
  intro t
  obtain ⟨W, xS, B, _, a, hxo, ⟨w0, hw0⟩, hB, hB'⟩ := h (T.hom t)
  refine ⟨pullback T.hom xS, pullback.fst T.hom xS, inferInstance,
    (range_of_isPullback (IsPullback.of_hasPullback T.hom xS) t).2 ⟨w0, hw0⟩, ?_⟩
  let TW : Over W := Over.mk (pullback.snd T.hom xS)
  have cx : (pullback.fst T.hom xS ≫ x.left) ≫ A.hom = pullback.snd T.hom xS ≫ xS := by
    rw [Category.assoc, Over.w x, pullback.condition]
  have cy : (pullback.fst T.hom xS ≫ y.left) ≫ A.hom = pullback.snd T.hom xS ≫ xS := by
    rw [Category.assoc, Over.w y, pullback.condition]
  have cx' : (pullback.fst T.hom xS ≫ x.left ≫ φ) ≫ A'.hom = pullback.snd T.hom xS ≫ xS := by
    simpa [w] using cx
  have cy' : (pullback.fst T.hom xS ≫ y.left ≫ φ) ≫ A'.hom = pullback.snd T.hom xS ≫ xS := by
    simpa [w] using cy
  let XB : TW ⟶ B := Over.homMk (hB.1.lift _ _ cx) (hB.1.lift_snd _ _ cx)
  let YB : TW ⟶ B := Over.homMk (hB.1.lift _ _ cy) (hB.1.lift_snd _ _ cy)
  let x' : Over.mk (TW.hom ≫ xS) ⟶ A := Over.homMk (pullback.fst T.hom xS ≫ x.left) cx
  let y' : Over.mk (TW.hom ≫ xS) ⟶ A := Over.homMk (pullback.fst T.hom xS ≫ y.left) cy
  let x₁ : Over.mk (TW.hom ≫ xS) ⟶ A' := Over.homMk (pullback.fst T.hom xS ≫ x.left ≫ φ) cx'
  let y₁ : Over.mk (TW.hom ≫ xS) ⟶ A' := Over.homMk (pullback.fst T.hom xS ≫ y.left ≫ φ) cy'
  have e1 : (x' * y').left = (XB * YB).left ≫ a :=
    hB.2 TW XB YB x' y' (hB.1.lift_fst _ _ cx).symm (hB.1.lift_fst _ _ cy).symm
  have e2 : (x₁ * y₁).left = (XB * YB).left ≫ a ≫ φ := by
    refine hB'.2 TW XB YB x₁ y₁ ?_ ?_
    · simp only [x₁, XB, Over.homMk_left]
      rw [← Category.assoc (hB.1.lift _ _ cx), hB.1.lift_fst, Category.assoc]
    · simp only [y₁, YB, Over.homMk_left]
      rw [← Category.assoc (hB.1.lift _ _ cy), hB.1.lift_fst, Category.assoc]
  have hk : pullback.fst T.hom xS ≫ T.hom = (Over.mk (TW.hom ≫ xS)).hom := by
    simp [TW, pullback.condition]
  have hk' : pullback.fst T.hom xS ≫ (Over.mk (T.hom ≫ 𝟙 S)).hom = (Over.mk (TW.hom ≫ xS)).hom := by
    simp [TW, pullback.condition]
  have m1 := mul_left_pre (pullback.fst T.hom xS) hk x y x' y' rfl rfl
  have m2 := mul_left_pre (pullback.fst T.hom xS) hk' x₀ y₀ x₁ y₁
    (by simp only [x₁, Over.homMk_left, hx]) (by simp only [y₁, Over.homMk_left, hy])
  rw [← m2, e2, ← Category.assoc, ← e1, m1, Category.assoc]

theorem isGrpPullback_local_on_base : ∀ (S : Scheme.{0}) (A A' : Over S) [GrpObj A] [GrpObj A'] (φ : A.left ⟶ A'.left), IsIso φ → φ ≫ A'.hom = A.hom → (∀ p : S, ∃ (V : Scheme.{0}) (x : V ⟶ S) (B : Over V) (_ : GrpObj B) (a : B.left ⟶ A.left), IsOpenImmersion x ∧ p ∈ Set.range x ∧ IsGrpPullback B A x a ∧ IsGrpPullback B A' x (a ≫ φ)) → IsGrpPullback A A' (𝟙 S) φ := by
  intro S A A' _ _ φ hφ w h
  exact isGrpPullback_id_of_loc φ w h

end GlobalTheory.GrpLoc
