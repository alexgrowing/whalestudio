import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

noncomputable section
namespace GlobalTheory.Ex.AbPartIso
variable {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
  {N N' : NumD F}

def HomF (φ : TF (R := R) F ⊗ D.P.A ≅ TF (R := R) F ⊗ D'.P.A) : Prop :=
  φ.hom ≫ fst _ _ = fst _ _ ∧ ∀ (Z : Over (Sp R)) (t : Z ⟶ TF (R := R) F) (x y : Z ⟶ D.P.A),
    lift t (x * y) ≫ φ.hom ≫ snd _ _ = (lift t x ≫ φ.hom ≫ snd _ _) * (lift t y ≫ φ.hom ≫ snd _ _)

abbrev BunIso (φ : TF (R := R) F ⊗ D.P.A ≅ TF (R := R) F ⊗ D'.P.A) : Type :=
  LB.Iso (D.P.L.pull (snd (TF (R := R) F) D.P.A).left) (D'.P.L.pull (φ.hom ≫ snd (TF (R := R) F) D'.P.A).left)

def Carries (ν : NumOf D F N) (ν' : NumOf D' F N') (φ : TF (R := R) F ⊗ D.P.A ≅ TF (R := R) F ⊗ D'.P.A)
    (x : N.A) (x' : N'.A) : Prop :=
  lift (𝟙 _) (ν.eA x) ≫ φ.hom = lift (𝟙 _) (ν'.eA x')

def wVal (ν : NumOf D F N) (ν' : NumOf D' F N') {φ : TF (R := R) F ⊗ D.P.A ≅ TF (R := R) F ⊗ D'.P.A} (w : BunIso φ)
    (f : N.A → N'.A) (x : N.A) : F :=
  valF (lift (𝟙 (TF (R := R) F)) (ν.eA x)).left _
    (w.s (fun _ => ν'.J (ν'.eA (f x)).left, fun _ => ν.J (ν.eA x).left)).val

def AllIso (P : ∀ {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
    {N N' : NumD F} (_ : NumOf D F N) (_ : NumOf D' F N') {φ : TF (R := R) F ⊗ D.P.A ≅ TF (R := R) F ⊗ D'.P.A},
    BunIso φ → (N.A → N'.A) → Prop) : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F]
    (N N' : NumD F) (ν : NumOf D F N) (ν' : NumOf D' F N') (φ : TF (R := R) F ⊗ D.P.A ≅ TF (R := R) F ⊗ D'.P.A)
    (w : BunIso φ) (f : N.A → N'.A), HomF φ → w.IsGen → (∀ x, Carries ν ν' φ x (f x)) → P ν ν' w f

def TorsMap {O : Type} [CommRing O] (B B' : NumB O) (m : ℕ) (c : O) (ρ : B.A → B'.A) : Prop :=
  (∀ b b', b ^ m ^ 2 = 1 → b' ^ m ^ 2 = 1 →
    ρ (b * b') = ρ b * ρ b' ∧ B'.weil (m ^ 2) (ρ b) (ρ b') = B.weil (m ^ 2) b b') ∧
  ∀ b, b ^ m ^ 2 = 1 → ρ b ^ m ^ 2 = 1 ∧ B'.uth m (ρ b) 1 = c * B.uth m b 1

def IsFib (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (Q : PolAV (Sp F))
    (Φ : Q.A.left ⟶ D.P.A.left) : Prop :=
  IsGrpPullback Q.A D.P.A (TF (R := R) F).hom Φ ∧ LBIso Q.L (D.P.L.pull Φ) ∧ Q.g = D.P.g

theorem exists_isFib (hB : PolBaseChangeSt) (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] :
    ∃ Q Φ, IsFib D F Q Φ := by
  obtain ⟨P', φ, hφ, hg, hm, ht⟩ := hB _ _ (TF (R := R) F).hom D.P
  refine ⟨P', φ, ⟨hφ, fun T x y x₀ y₀ hx hy => ?_⟩, LBIso.symm ht, hg⟩
  rw [(Over.OverMorphism.ext hx : x₀ = Out.toBase hφ.w x), (Over.OverMorphism.ext hy : y₀ = Out.toBase hφ.w y), ← hm]
  rfl

end GlobalTheory.Ex.AbPartIso
end
