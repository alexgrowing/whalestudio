import Mathlib
import Development.AbelianVarietyTheory.Statements.LocalTrivialization.LocTrivOfRetraction
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.TorusQuotientTorsionLift
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FlatQuotientIsoOfSameKernel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.TQCompare
open GlobalTheory.UU GlobalTheory.IndefiniteRowSideFullHecke.TorusQuotientTorsionLift

section Clauses
variable {S S' : Scheme.{0}} {X : Type} [AddCommGroup X]

theorem isGrpPullback_id_iff {B B' : Over S} [GrpObj B] [GrpObj B'] (β : B.left ⟶ B'.left) :
    IsGrpPullback B B' (𝟙 S) β ↔ ∃ e : B ≅ B', IsMonHom e.hom ∧ e.hom.left = β := by
  constructor
  · rintro ⟨hpb, hmul⟩
    have : IsIso β := hpb.isIso_fst_of_isIso
    have hw : β ≫ B'.hom = B.hom := by simpa using hpb.w
    obtain ⟨e, he⟩ : ∃ e : B ≅ B', e.hom.left = β := ⟨Over.isoMk (asIso β) hw, rfl⟩
    have key : ∀ (T : Over S) (x y : T ⟶ B), (x * y) ≫ e.hom = (x ≫ e.hom) * (y ≫ e.hom) := by
      intro T x y
      have h1 := hmul T x y (Over.homMk (x.left ≫ β) (by simp [hw])) (Over.homMk (y.left ≫ β) (by simp [hw]))
        rfl rfl
      apply Over.OverMorphism.ext
      simp only [Hom.mul_def, Over.comp_left, Over.lift_left, Over.homMk_left, Category.assoc, he] at h1 ⊢
      exact h1.symm
    have hone : ∀ {M : Over S} [GrpObj M], (1 : 𝟙_ (Over S) ⟶ M) = η[M] := by
      intro M _
      rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
    refine ⟨e, ⟨?_, ?_⟩, he⟩
    · have h2 := key (𝟙_ (Over S)) 1 1
      rw [_root_.one_mul] at h2
      have h3 : (1 : 𝟙_ (Over S) ⟶ B) ≫ e.hom = 1 := _root_.mul_left_cancel (h2.symm.trans (_root_.mul_one _).symm)
      rw [hone, hone] at h3
      exact h3
    · have h3 := key _ (fst B B) (snd B B)
      rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp] at h3
      rw [h3]
      congr 1
  · rintro ⟨e, he, rfl⟩
    have : IsIso e.hom.left := (Over.forget S).map_isIso e.hom
    refine ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, ?_⟩
    intro T x y x₀ y₀ hx hy
    have hm := (IsMonHom.monoidHom e.hom T).map_mul x y
    simp only [IsMonHom.monoidHom_apply] at hm
    have h4 := congrArg Over.Hom.left hm
    simp only [Hom.mul_def, Over.comp_left, Over.lift_left, Category.assoc] at h4 ⊢
    simp only [hx, hy]
    exact h4.symm

end Clauses

section At
variable (X : Type) [AddCommGroup X]

def ActGradeAt : Prop := ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G]
  (i : splitTorus S X ⟶ G), IsMonHom i → ∀ V : G.left.Opens, IsAffineOpen V →
  (snd (splitTorus S X) G).left ⁻¹ᵁ V ≤ ((fst (splitTorus S X) G ≫ i) * snd (splitTorus S X) G).left ⁻¹ᵁ V →
  (∀ u : Γ(G.left, V), ∃ a : X →₀ Γ(G.left, V), (∀ χ, IsWt i V (a χ) χ) ∧ u = a.sum fun _ x => x) ∧
  ∀ a : X →₀ Γ(G.left, V), (∀ χ, IsWt i V (a χ) χ) → (a.sum fun _ x => x) = 0 → a = 0

def TQUniqAt : Prop := ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (G : Over S) [GrpObj G]
  (G' : Over S') [GrpObj G'] (F : G'.left ⟶ G.left), IsGrpPullback G' G f F → ∀ (Q : TQ G X) (Q' : TQ G' X),
  TorusCompat f F Q'.i Q.i → ∃ β : Q'.B.left ⟶ Q.B.left, Q'.q.left ≫ β = F ≫ Q.q.left ∧ IsGrpPullback Q'.B Q.B f β

def TQUniqIdAt : Prop := ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (Q Q' : TQ G X),
  TorusCompat (𝟙 S) (𝟙 G.left) Q'.i Q.i →
    ∃ β : Q'.B.left ⟶ Q.B.left, Q'.q.left ≫ β = 𝟙 G.left ≫ Q.q.left ∧ IsGrpPullback Q'.B Q.B (𝟙 S) β

def TQBaseAt : Prop := ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (G : Over S) [GrpObj G]
  (G' : Over S') [GrpObj G'] (F : G'.left ⟶ G.left), IsGrpPullback G' G f F → ∀ Q : TQ G X,
  ∃ Q' : TQ G' X, TorusCompat f F Q'.i Q.i

end At

def ForAllGroups (P : ∀ (X : Type) [AddCommGroup X], Prop) : Prop := ∀ (X : Type) [AddCommGroup X], P X

def ForLattices (P : ∀ (X : Type) [AddCommGroup X], Prop) : Prop :=
  ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X], P X

def PointLiftComm : Prop :=
  ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (X : Type) [AddCommGroup X] [Module.Free ℤ X]
    [Module.Finite ℤ X] (Q : TQ G X) (R : Type) [CommRing R] [IsLocalRing R] (p : Spec (CommRingCat.of R) ⟶ S)
    (b : pt p ⟶ Q.B), ∃ x : pt p ⟶ G, x ≫ Q.q = b

def TQDimOfExists : Prop :=
  ∀ (S : Scheme.{0}) [Nonempty S] (G : Over S) [GrpObj G] (X : Type) [AddCommGroup X] [Module.Free ℤ X]
    [Module.Finite ℤ X] (Q : TQ G X), (∃ g, SmoothOfRelativeDimension g G.hom) →
    (∃ g', SmoothOfRelativeDimension g' Q.B.hom) →
    (∀ g' : ℕ, SmoothOfRelativeDimension (g' + Module.finrank ℤ X) G.hom ↔ SmoothOfRelativeDimension g' Q.B.hom) ∧
    (Nonempty S → ∀ g : ℕ, SmoothOfRelativeDimension g G.hom → Module.finrank ℤ X ≤ g)

def QuotSchemeLocal : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] (J : Ideal A), IsNilpotent J →
  ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (G : Over (Spec (CommRingCat.of A))) [GrpObj G]
  [IsCommMonObj G] [Smooth G.hom] (G₀ : Over (Spec (CommRingCat.of (A ⧸ J)))) [GrpObj G₀] (F : G₀.left ⟶ G.left),
  IsGrpPullback G₀ G (red J) F → ∀ (Q₀ : TQ G₀ X) (i : splitTorus _ X ⟶ G), IsMonHom i → TorusCompat (red J) F Q₀.i i →
  ∃ (B : Over (Spec (CommRingCat.of A))) (q : G ⟶ B) (j : Q₀.B.left ⟶ B.left),
    IsPullback j Q₀.B.hom B.hom (red J) ∧ Q₀.q.left ≫ j = F ≫ q.left ∧ IsAffineHom q.left ∧
    ∀ b : B.left, ∃ V : B.left.Opens, b ∈ V ∧ IsAffineOpen V ∧
      (∀ a : Γ(G.left, q.left ⁻¹ᵁ V), IsWt i _ a 0 ↔ ∃ c, (q.left.app V).hom c = a) ∧ Function.Injective (q.left.app V).hom ∧
      (snd (splitTorus _ X) G).left ⁻¹ᵁ (q.left ⁻¹ᵁ V) ≤ ((fst (splitTorus _ X) G ≫ i) * snd _ G).left ⁻¹ᵁ (q.left ⁻¹ᵁ V) ∧
      ∃ u : Multiplicative X →* Γ(G.left, q.left ⁻¹ᵁ V)ˣ, ∀ χ, IsWt i _ (u (Multiplicative.ofAdd χ)).val χ

end GlobalTheory.TQCompare
end
