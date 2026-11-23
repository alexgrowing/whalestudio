import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsTjCorrDiagModel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

noncomputable section

namespace UpperTheory.ES

def KerIs (H : Type) [CommGroup H] {T : Scheme.{0}} {A B : Over T} [GrpObj A] [GrpObj B] (ψ : A ⟶ B)
    {k : Type} [Field k] (x : Sp k ⟶ T) : Prop :=
  ∃ f : H → (Over.mk x ⟶ A), (∀ a c, f (a * c) = f a * f c) ∧ Function.Injective f ∧
    ∀ g : Over.mk x ⟶ A, g ≫ ψ = 1 ↔ g ∈ Set.range f

def KerIn (C : Set (Σ H : Type, CommGroup H)) {T : Scheme.{0}} {A B : Over T} [GrpObj A] [GrpObj B]
    (ψ : A ⟶ B) : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ T), ∃ t ∈ C, @KerIs t.1 t.2 T A B _ _ ψ k _ x

def HasFam {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ} {S : Scheme.{0}}
    {s : S ⟶ Sp R} (o : Obj b N s) (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ)
    (C : Set (Σ H : Type, CommGroup H)) : Prop :=
  ∃ (Y : Over S) (o₀ : Obj b N (Y.hom ≫ s)) (m₀ : ObjMap o₀ o Y.hom) (o' : Obj b N (Y.hom ≫ s))
    (ψ : o₀.A ⟶ o'.A), IsFinite Y.hom ∧ Etale Y.hom ∧ IsPIsog c o₀ o' ψ ∧ IsTj r w j o₀ o' ψ ∧ KerIn C ψ ∧
    ∀ (T : Scheme.{0}) (x : T ⟶ S) (o₁ o₁' : Obj b N (x ≫ s)) (m : ObjMap o₁ o x) (ψ₁ : o₁.A ⟶ o₁'.A),
      IsPIsog c o₁ o₁' ψ₁ → IsTj r w j o₁ o₁' ψ₁ → KerIn C ψ₁ →
      ∃! y : T ⟶ Y.left, y ≫ Y.hom = x ∧ ∃ (m₀' : ObjMap o₁ o₀ y) (m₁ : ObjMap o₁' o' y),
        m₀'.φ ≫ ψ.left = ψ₁.left ≫ m₁.φ

def GrpIso (t t' : Σ H : Type, CommGroup H) : Prop :=
  letI := t.2
  letI := t'.2
  Nonempty (t.1 ≃* t'.1)

end UpperTheory.ES
