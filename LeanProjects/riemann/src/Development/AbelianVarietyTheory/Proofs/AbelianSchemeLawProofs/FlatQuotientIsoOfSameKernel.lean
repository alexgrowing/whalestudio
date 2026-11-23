import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegExp

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace FlatQuotient

variable {S : Scheme.{0}}

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
attribute [local instance] Over.cartesianMonoidalCategory in
variable {S : Scheme.{0}} in

lemma _root_.GlobalTheory.FlatQuotient.epi_of_flat_surjective {X Y : Over S} (f : X ⟶ Y) [Flat f.left] [Surjective f.left] :
    Epi f := by
  have hepi : Epi f.left := Flat.epi_of_flat_of_surjective f.left
  exact (Over.forget S).epi_of_epi_map hepi

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
attribute [local instance] Over.cartesianMonoidalCategory in
variable {S : Scheme.{0}} in
private lemma whiskerRight_left_of_isStableUnderBaseChange (P : MorphismProperty Scheme.{0})
    [P.IsStableUnderBaseChange] {X Y : Over S} (f : X ⟶ Y) (Z : Over S) (hf : P f.left) :
    P (f ▷ Z).left := by
  have e1 : (f ▷ Z).left ≫ pullback.snd Y.hom Z.hom = pullback.snd X.hom Z.hom := by
    rw [Over.whiskerRight_left]
    exact (pullback.lift_snd _ _ _).trans (by simp)
  have e2 : (f ▷ Z).left ≫ pullback.fst Y.hom Z.hom = pullback.fst X.hom Z.hom ≫ f.left := by
    rw [Over.whiskerRight_left]
    exact (pullback.lift_fst _ _ _).trans (by simp)
  have houter : IsPullback ((f ▷ Z).left ≫ pullback.snd Y.hom Z.hom) (pullback.fst X.hom Z.hom)
      Z.hom (f.left ≫ Y.hom) := by
    rw [e1, Over.w f]
    exact (IsPullback.of_hasPullback X.hom Z.hom).flip
  exact MorphismProperty.of_isPullback
    (IsPullback.of_right houter e2 (IsPullback.of_hasPullback Y.hom Z.hom).flip).flip hf

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
attribute [local instance] Over.cartesianMonoidalCategory in
variable {S : Scheme.{0}} in
private lemma whiskerLeft_left_of_isStableUnderBaseChange (P : MorphismProperty Scheme.{0})
    [P.IsStableUnderBaseChange] {X Y : Over S} (Z : Over S) (f : X ⟶ Y) (hf : P f.left) :
    P (Z ◁ f).left := by
  have e1 : (Z ◁ f).left ≫ pullback.fst Z.hom Y.hom = pullback.fst Z.hom X.hom := by
    rw [Over.whiskerLeft_left]
    exact (pullback.lift_fst _ _ _).trans (by simp)
  have e2 : (Z ◁ f).left ≫ pullback.snd Z.hom Y.hom = pullback.snd Z.hom X.hom ≫ f.left := by
    rw [Over.whiskerLeft_left]
    exact (pullback.lift_snd _ _ _).trans (by simp)
  have houter : IsPullback ((Z ◁ f).left ≫ pullback.fst Z.hom Y.hom) (pullback.snd Z.hom X.hom)
      Z.hom (f.left ≫ Y.hom) := by
    rw [e1, Over.w f]
    exact IsPullback.of_hasPullback Z.hom X.hom
  exact MorphismProperty.of_isPullback
    (IsPullback.of_right houter e2 (IsPullback.of_hasPullback Z.hom Y.hom)).flip hf

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
attribute [local instance] Over.cartesianMonoidalCategory in
variable {S : Scheme.{0}} in

lemma _root_.GlobalTheory.FlatQuotient.epi_tensorHom {X Y X' Y' : Over S} (f : X ⟶ Y) (g : X' ⟶ Y')
    [hf : Flat f.left] [hf' : Surjective f.left] [hg : Flat g.left] [hg' : Surjective g.left] :
    Epi (f ⊗ₘ g) := by
  have h₁ : Flat (f ▷ X').left := whiskerRight_left_of_isStableUnderBaseChange @Flat f X' hf
  have h₂ : Surjective (f ▷ X').left := whiskerRight_left_of_isStableUnderBaseChange @Surjective f X' hf'
  have h₃ : Flat (Y ◁ g).left := whiskerLeft_left_of_isStableUnderBaseChange @Flat Y g hg
  have h₄ : Surjective (Y ◁ g).left := whiskerLeft_left_of_isStableUnderBaseChange @Surjective Y g hg'
  have e₁ := _root_.GlobalTheory.FlatQuotient.epi_of_flat_surjective (f ▷ X')
  have e₂ := _root_.GlobalTheory.FlatQuotient.epi_of_flat_surjective (Y ◁ g)
  rw [MonoidalCategory.tensorHom_def]
  exact epi_comp _ _

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
attribute [local instance] Over.cartesianMonoidalCategory in
variable {S : Scheme.{0}} in

lemma _root_.GlobalTheory.FlatQuotient.comp_eq_of_kills_kernel {G B B' T : Over S} [GrpObj G] [GrpObj B] [GrpObj B']
    (q : G ⟶ B) (i : T ⟶ G) (f : G ⟶ B') [IsMonHom q] [IsMonHom f]
    (hker : IsPullback i (toUnit _) q (η[B])) (hf : i ≫ f = toUnit _ ≫ η[B'])
    {Z : Over S} (g g' : Z ⟶ G) (h : g ≫ q = g' ≫ q) : g ≫ f = g' ≫ f := by
  have hk : (g * g'⁻¹) ≫ q = toUnit Z ≫ η[B] := by
    rw [mul_comp, GrpObj.inv_comp, h, mul_inv_cancel, Hom.one_def]
  have hl : hker.lift (g * g'⁻¹) (toUnit Z) hk ≫ i = g * g'⁻¹ := hker.lift_fst _ _ _
  have hone : (g * g'⁻¹) ≫ f = 1 := by
    rw [← hl, Category.assoc, hf, Hom.one_def, ← Category.assoc, toUnit_unique
      (hker.lift (g * g'⁻¹) (toUnit Z) hk ≫ toUnit T) (toUnit Z)]
  rw [mul_comp, GrpObj.inv_comp, mul_inv_eq_one] at hone
  exact hone

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
attribute [local instance] Over.cartesianMonoidalCategory in
variable {S : Scheme.{0}} in

theorem _root_.GlobalTheory.FlatQuotient.exists_desc {G B B' T : Over S} [GrpObj G]
    [GrpObj B] [GrpObj B'] (q : G ⟶ B) (i : T ⟶ G) (f : G ⟶ B') [IsMonHom q] [IsMonHom f]
    [Flat q.left] [Surjective q.left] [QuasiCompact q.left]
    (hker : IsPullback i (toUnit _) q (η[B])) (hf : i ≫ f = toUnit _ ≫ η[B']) :
    ∃ β : B ⟶ B', IsMonHom β ∧ q ≫ β = f := by
  have hcomp : ∀ {Z : Scheme} (g₁ g₂ : Z ⟶ G.left), g₁ ≫ q.left = g₂ ≫ q.left →
      g₁ ≫ f.left = g₂ ≫ f.left := by
    intro Z g₁ g₂ h
    have hw : g₂ ≫ G.hom = g₁ ≫ G.hom := by
      rw [← Over.w q, ← Category.assoc, ← h, Category.assoc]
    have key := _root_.GlobalTheory.FlatQuotient.comp_eq_of_kills_kernel q i f hker hf (Z := Over.mk (g₁ ≫ G.hom))
      (Over.homMk g₁) (Over.homMk g₂ hw) (by ext; simpa using h)
    simpa using congrArg (fun φ => φ.left) key
  let β₀ : B.left ⟶ B'.left := EffectiveEpi.desc q.left f.left hcomp
  have hβ₀ : q.left ≫ β₀ = f.left := EffectiveEpi.fac _ _ _
  have hw : β₀ ≫ B'.hom = B.hom := by
    rw [← cancel_epi q.left, reassoc_of% hβ₀, Over.w f, Over.w q]
  let β : B ⟶ B' := Over.homMk β₀ hw
  have hqβ : q ≫ β = f := by
    ext
    simp [β, hβ₀]
  have hqq : Epi (q ⊗ₘ q) := _root_.GlobalTheory.FlatQuotient.epi_tensorHom q q
  refine ⟨β, ⟨?_, ?_⟩, hqβ⟩
  · rw [← IsMonHom.one_hom (f := q), Category.assoc, hqβ, IsMonHom.one_hom]
  · rw [← cancel_epi (q ⊗ₘ q)]
    calc (q ⊗ₘ q) ≫ μ ≫ β = μ ≫ q ≫ β := by
          rw [← Category.assoc, ← IsMonHom.mul_hom, Category.assoc]
      _ = μ ≫ f := by rw [hqβ]
      _ = (f ⊗ₘ f) ≫ μ := IsMonHom.mul_hom f
      _ = (q ⊗ₘ q) ≫ (β ⊗ₘ β) ≫ μ := by
          rw [← hqβ]
          simp

end FlatQuotient

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
attribute [local instance] Over.cartesianMonoidalCategory in

theorem _root_.GlobalTheory.flatQuotient_iso_of_same_kernel :
    ∀ (S : Scheme.{0}) (G B B' T T' : Over S) [GrpObj G] [GrpObj B] [GrpObj B'] [GrpObj T]
      [GrpObj T'] (q : G ⟶ B) (i : T ⟶ G) (q' : G ⟶ B') (i' : T' ⟶ G),
      IsMonHom q → IsMonHom i → Flat q.left → Surjective q.left → QuasiCompact q.left →
      IsPullback i (toUnit _) q (η[B]) → IsMonHom q' → IsMonHom i' → Flat q'.left →
      Surjective q'.left → QuasiCompact q'.left → IsPullback i' (toUnit _) q' (η[B']) →
      i' ≫ q = toUnit _ ≫ η[B] → i ≫ q' = toUnit _ ≫ η[B'] →
      ∃ β : B' ≅ B, IsMonHom β.hom ∧ q' ≫ β.hom = q := by
  intro S G B B' T T' _ _ _ _ _ q i q' i' hq _ hqf hqs hqc hk hq' _ hq'f hq's hq'c hk' h₁ h₂
  obtain ⟨β, -, hqβ⟩ := _root_.GlobalTheory.FlatQuotient.exists_desc q i q' hk h₂
  obtain ⟨β', hβ', hq'β'⟩ := _root_.GlobalTheory.FlatQuotient.exists_desc q' i' q hk' h₁
  have eq : Epi q := _root_.GlobalTheory.FlatQuotient.epi_of_flat_surjective q
  have eq' : Epi q' := _root_.GlobalTheory.FlatQuotient.epi_of_flat_surjective q'
  have e₁ : β ≫ β' = 𝟙 B := by
    rw [← cancel_epi q, reassoc_of% hqβ, hq'β', Category.comp_id]
  have e₂ : β' ≫ β = 𝟙 B' := by
    rw [← cancel_epi q', reassoc_of% hq'β', hqβ, Category.comp_id]
  exact ⟨⟨β', β, e₂, e₁⟩, hβ', hq'β'⟩

end GlobalTheory
