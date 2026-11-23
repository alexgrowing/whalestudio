import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsRepresentableOfCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.EndLoc.HomFixGlue

variable {S : Scheme.{0}}

def cmp (X : Over S) {T T' : Scheme.{0}} (c : T' ⟶ T) (t : T ⟶ S) :
    pullback X.hom (c ≫ t) ⟶ pullback X.hom t :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ c) (by rw [pullback.condition, Category.assoc])

@[reassoc (attr := simp)]
theorem cmp_fst (X : Over S) {T T' : Scheme.{0}} (c : T' ⟶ T) (t : T ⟶ S) :
    cmp X c t ≫ pullback.fst X.hom t = pullback.fst X.hom (c ≫ t) := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem cmp_snd (X : Over S) {T T' : Scheme.{0}} (c : T' ⟶ T) (t : T ⟶ S) :
    cmp X c t ≫ pullback.snd X.hom t = pullback.snd X.hom (c ≫ t) ≫ c := pullback.lift_snd _ _ _

variable (A B : Over S) [GrpObj A] [GrpObj B]

def baseHom {T T' : Scheme.{0}} (c : T' ⟶ T) (t : T ⟶ S)
    (Φ : (Over.pullback t).obj A ⟶ (Over.pullback t).obj B) :
    (Over.pullback (c ≫ t)).obj A ⟶ (Over.pullback (c ≫ t)).obj B :=
  Over.homMk (pullback.lift (cmp A c t ≫ Φ.left ≫ pullback.fst B.hom t) (pullback.snd A.hom (c ≫ t)) (by
    have h1 : Φ.left ≫ pullback.snd B.hom t = pullback.snd A.hom t := Over.w Φ
    rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc Φ.left, h1, cmp_snd_assoc]))
    (pullback.lift_snd _ _ _)

@[reassoc (attr := simp)]
theorem baseHom_fst {T T' : Scheme.{0}} (c : T' ⟶ T) (t : T ⟶ S)
    (Φ : (Over.pullback t).obj A ⟶ (Over.pullback t).obj B) :
    (baseHom A B c t Φ).left ≫ pullback.fst B.hom (c ≫ t) = cmp A c t ≫ Φ.left ≫ pullback.fst B.hom t :=
  pullback.lift_fst _ _ _

abbrev Pair (T : Scheme.{0}) : Type := Σ t : T ⟶ S, (Over.pullback t).obj A ⟶ (Over.pullback t).obj B

theorem pair_ext {T : Scheme.{0}} {t₁ t₂ : T ⟶ S} (h : t₁ = t₂)
    (Φ₁ : (Over.pullback t₁).obj A ⟶ (Over.pullback t₁).obj B)
    (Φ₂ : (Over.pullback t₂).obj A ⟶ (Over.pullback t₂).obj B)
    (hΦ : Φ₁.left ≫ pullback.fst B.hom t₁ =
      pullback.map A.hom t₁ A.hom t₂ (𝟙 _) (𝟙 _) (𝟙 _) (by simp) (by simp [h]) ≫ Φ₂.left ≫ pullback.fst B.hom t₂) :
    (⟨t₁, Φ₁⟩ : Pair A B T) = ⟨t₂, Φ₂⟩ := by
  subst h
  have e : pullback.map A.hom t₁ A.hom t₁ (𝟙 _) (𝟙 _) (𝟙 _) (by simp) (by simp) = 𝟙 _ := by
    apply pullback.hom_ext <;> simp
  rw [e, Category.id_comp] at hΦ
  congr 1
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · exact hΦ
  · exact (Over.w Φ₁).trans (Over.w Φ₂).symm

abbrev basePair {T T' : Scheme.{0}} (c : T' ⟶ T) (p : Pair A B T) : Pair A B T' :=
  ⟨c ≫ p.1, baseHom A B c p.1 p.2⟩

theorem basePair_id {T : Scheme.{0}} (p : Pair A B T) : basePair A B (𝟙 T) p = p := by
  obtain ⟨t, Φ⟩ := p
  refine pair_ext A B (Category.id_comp t) _ _ ?_
  simp only [basePair, baseHom_fst]
  congr 1

theorem basePair_comp {T T' T'' : Scheme.{0}} (c : T' ⟶ T) (c' : T'' ⟶ T') (p : Pair A B T) :
    basePair A B (c' ≫ c) p = basePair A B c' (basePair A B c p) := by
  obtain ⟨t, Φ⟩ := p
  refine pair_ext A B (Category.assoc c' c t) _ _ ?_
  have e : pullback.map A.hom ((c' ≫ c) ≫ t) A.hom (c' ≫ c ≫ t) (𝟙 _) (𝟙 _) (𝟙 _) (by simp) (by simp) ≫
      cmp A c' (c ≫ t) ≫ cmp A c t = cmp A (c' ≫ c) t := by
    apply pullback.hom_ext
    · simp [pullback.map]
      exact pullback.lift_fst _ _ _
    · simp [pullback.map]
      exact pullback.lift_snd_assoc _ _ _ _
  simp only [basePair, baseHom_fst, baseHom_fst_assoc]
  rw [← e]
  simp only [Category.assoc]

variable (L : LB A.left) (M : LB B.left)

def Good {T : Scheme.{0}} (p : Pair A B T) : Prop :=
  IsMonHom p.2 ∧ LBIso (L.pull (pullback.fst A.hom p.1)) ((M.pull (pullback.fst B.hom p.1)).pull p.2.left)

def Good' {T : Scheme.{0}} (p : Pair A B T) : Prop :=
  ∀ (T' : Scheme.{0}) (c : T' ⟶ T), Good A B L M (basePair A B c p)

theorem good'_basePair {T T' : Scheme.{0}} (c : T' ⟶ T) {p : Pair A B T} (h : Good' A B L M p) :
    Good' A B L M (basePair A B c p) := fun T'' c' => by
  rw [← basePair_comp]; exact h T'' (c' ≫ c)

def homFixFunctor : Scheme.{0}ᵒᵖ ⥤ Type where
  obj T := {p : Pair A B T.unop // Good' A B L M p}
  map c := TypeCat.ofHom fun p => ⟨basePair A B c.unop p.1, good'_basePair A B L M c.unop p.2⟩
  map_id T := by
    apply ConcreteCategory.hom_ext
    intro p
    exact Subtype.ext (basePair_id A B p.1)
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro p
    exact Subtype.ext (basePair_comp A B f.unop g.unop p.1)

@[simp]
theorem homFixFunctor_map_val {T T' : Scheme.{0}ᵒᵖ} (c : T ⟶ T') (p : (homFixFunctor A B L M).obj T) :
    ((homFixFunctor A B L M).map c p).1 = basePair A B c.unop p.1 := rfl

def homFixProj : homFixFunctor A B L M ⟶ yoneda.obj S where
  app T := TypeCat.ofHom fun p => p.1.1

end GlobalTheory.EndLoc.HomFixGlue

namespace GlobalTheory.EndLoc.HomFixGlue
@[simp]
theorem homFixProj_app {S : Scheme.{0}} (A B : Over S) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left)
    {T : Scheme.{0}ᵒᵖ} (p : (homFixFunctor A B L M).obj T) : (homFixProj A B L M).app T p = p.1.1 := rfl
end GlobalTheory.EndLoc.HomFixGlue
