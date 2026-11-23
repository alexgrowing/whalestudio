import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.EndLoc

variable {S : Scheme.{0}}

structure HomFixRep (A B : Over S) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left) where
  H : Scheme.{0}
  π : H ⟶ S
  AH : Over H
  [grpA : GrpObj AH]
  BH : Over H
  [grpB : GrpObj BH]
  φA : AH.left ⟶ A.left
  φB : BH.left ⟶ B.left
  pbA : IsGrpPullback AH A π φA
  pbB : IsGrpPullback BH B π φB
  Φ : AH ⟶ BH
  hom : IsMonHom Φ
  iso : LBIso (L.pull φA) ((M.pull φB).pull Φ.left)
  rep : ∀ (T : Scheme.{0}) (t : T ⟶ S) (A' B' : Over T) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left)
    (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B'), IsGrpPullback A' A t φA' → IsGrpPullback B' B t φB' → IsMonHom Φ' →
    LBIso (L.pull φA') ((M.pull φB').pull Φ'.left) →
    ∃! h : T ⟶ H, h ≫ π = t ∧ ∃ (ψA : A'.left ⟶ AH.left) (ψB : B'.left ⟶ BH.left), IsGrpPullback A' AH h ψA ∧
      IsGrpPullback B' BH h ψB ∧ ψA ≫ φA = φA' ∧ ψB ≫ φB = φB' ∧ Φ'.left ≫ ψB = ψA ≫ Φ.left

attribute [instance] HomFixRep.grpA HomFixRep.grpB

theorem isGrpPullback_id (A : Over S) [GrpObj A] : IsGrpPullback A A (𝟙 S) (𝟙 A.left) := by
  refine ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, ?_⟩
  intro T x y x₀ y₀ hx hy
  let e : T ⟶ Over.mk (T.hom ≫ 𝟙 S) := Over.homMk (𝟙 _) (by simp)
  have h1 : e ≫ x₀ = x := by ext; simp [e, hx]
  have h2 : e ≫ y₀ = y := by ext; simp [e, hy]
  have h3 : e ≫ (x₀ * y₀) = x * y := by rw [MonObj.comp_mul, h1, h2]
  rw [← h3]; simp [e]

def HomFixRep.toTrivial (A : Over S) [GrpObj A] (L : LB A.left) (M : LB (𝟙_ (Over S)).left)
    (h : LBIso (L.pull (𝟙 _)) ((M.pull (𝟙 _)).pull (toUnit A).left)) : HomFixRep A (𝟙_ (Over S)) L M where
  H := S
  π := 𝟙 S
  AH := A
  BH := 𝟙_ (Over S)
  φA := 𝟙 _
  φB := 𝟙 _
  pbA := isGrpPullback_id A
  pbB := isGrpPullback_id _
  Φ := toUnit A
  hom := inferInstance
  iso := h
  rep := by
    intro T t A' B' _ _ φA' φB' Φ' hA hB _ _
    refine ⟨t, ⟨by simp, φA', φB', hA, hB, by simp, by simp, ?_⟩, fun h hh => by simpa using hh.1⟩
    have h1 := hA.1.w
    have h2 := hB.1.w
    have h3 := Over.w Φ'
    have h4 := Over.w (toUnit A)
    have h5 : φB' = B'.hom ≫ t := by simpa using h2
    have h6 : (toUnit A).left = A.hom := by simpa using h4
    rw [h5, h6, ← Category.assoc, h3]; exact h1.symm

def trivLB (X : Scheme.{0}) : LB X where
  «ι» := PUnit
  U := fun _ => ⊤
  g := fun _ _ => 1

theorem trivLB_isLB (X : Scheme.{0}) : (trivLB X).IsLB :=
  ⟨by simp [trivLB], fun _ => map_one _, fun _ _ _ =>
    (congrArg₂ (· * ·) (map_one _) (map_one _)).trans ((_root_.mul_one _).trans (map_one _).symm)⟩

theorem pull_g_one {X Y : Scheme.{0}} (L : LB X) (h : ∀ i j, L.g i j = 1) (f : Y ⟶ X) (i j) :
    (L.pull f).g i j = 1 := by
  dsimp only [LB.pull, LB.LinComb]
  erw [Finset.prod_eq_one]
  · rfl
  intro k _
  rw [h, map_one]; erw [map_one]; exact _root_.one_zpow _

theorem lbIso_of_g_one {X : Scheme.{0}} (L M : LB X) (hL : ∀ i j, L.g i j = 1) (hM : ∀ i j, M.g i j = 1) :
    LBIso L M := by
  refine ⟨⟨fun _ => 1⟩, fun i j => ?_⟩
  have : (LB.div M L).g i j = 1 := by
    simp only [LB.div, hL, hM, map_one, inv_one, _root_.mul_one]; rfl
  rw [this, map_one, map_one, _root_.mul_one]

theorem nonempty_homFixRep_trivial (A : Over S) [GrpObj A] :
    Nonempty (HomFixRep A (𝟙_ (Over S)) (trivLB _) (trivLB _)) :=
  ⟨HomFixRep.toTrivial A _ _ (lbIso_of_g_one _ _ (pull_g_one _ (fun _ _ => rfl) _)
    (pull_g_one _ (pull_g_one _ (fun _ _ => rfl) _) _))⟩

def HomFixRep.fromTrivial (B : Over S) [GrpObj B] (L : LB (𝟙_ (Over S)).left) (M : LB B.left)
    (h : LBIso (L.pull (𝟙 _)) ((M.pull (𝟙 _)).pull (η[B]).left)) : HomFixRep (𝟙_ (Over S)) B L M where
  H := S
  π := 𝟙 S
  AH := 𝟙_ (Over S)
  BH := B
  φA := 𝟙 _
  φB := 𝟙 _
  pbA := isGrpPullback_id _
  pbB := isGrpPullback_id B
  Φ := η[B]
  hom := inferInstance
  iso := h
  rep := by
    intro T t A' B' _ _ φA' φB' Φ' hA hB hΦ _
    refine ⟨t, ⟨by simp, φA', φB', hA, hB, by simp, by simp, ?_⟩, fun h hh => by simpa using hh.1⟩
    have h1 : φA' = A'.hom ≫ t := by simpa using hA.1.w
    have hiso : IsIso A'.hom := by
      have : IsIso (𝟙_ (Over S)).hom := by simp; infer_instance
      exact hA.1.isIso_snd_of_isIso
    have hu : 𝟙 A' = (1 : A' ⟶ A') := by
      ext; rw [← cancel_mono A'.hom]; simp
    have hΦ1 : Φ' = (1 : A' ⟶ B') := by
      rw [← Category.id_comp Φ', hu]; simp [Hom.one_def]
    let x₀ : Over.mk (A'.hom ≫ t) ⟶ B := Over.homMk (Φ'.left ≫ φB') (by simp [hB.1.w])
    have hm := hB.2 A' Φ' Φ' x₀ x₀ rfl rfl
    have hx : x₀ * x₀ = x₀ := by
      ext; rw [hm]; simp [x₀, hΦ1]
    have hx1 : x₀ = 1 := by simpa using hx
    have := congrArg (fun f => f.left) hx1
    simp only [x₀, Over.homMk_left] at this
    rw [this, h1]; simp [Hom.one_def]

example (A : Over S) [GrpObj A] (L : LB A.left) (M : LB (𝟙_ (Over S)).left)
    (h : LBIso (L.pull (𝟙 _)) ((M.pull (𝟙 _)).pull (toUnit A).left)) :
    (HomFixRep.toTrivial A L M h).H = S := rfl

example : (trivLB S).IsLB := trivLB_isLB S

end GlobalTheory.EndLoc
