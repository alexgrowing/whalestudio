import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ConstGen
import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.BaseChangeMapRingAct

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open ReciprocityTheory.ChartRestriction.G.Out (RelAmple)
open GlobalTheory.PDiv GlobalTheory.PDivGroup

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SerreTate

abbrev IsRed {R : Type} [CommRing R] (I : Ideal R) (A₀ : Over (Sp (R ⧸ I))) [GrpObj A₀] (A : Over (Sp R))
    [GrpObj A] (φ : A₀.left ⟶ A.left) : Prop :=
  IsGrpPullback A₀ A (spMap (algebraMap R (R ⧸ I))) φ

def TowerRed {p : ℕ} {R : Type} [CommRing R] {I : Ideal R} {A₀ : Over (Sp (R ⧸ I))} [GrpObj A₀] {A : Over (Sp R)}
    [GrpObj A] (φ : A₀.left ⟶ A.left) {G : PDivGroup p R} {G₀ : PDivGroup p (R ⧸ I)}
    (s : SemiHom (algebraMap R (R ⧸ I)) G₀ G) (t : G.TorsionTower A) (t₀ : G₀.TorsionTower A₀) : Prop :=
  ∀ n, spMap (s.app n).toRingHom ≫ (t.y n).left = (t₀.y n).left ≫ φ

def HomLift : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (I : Ideal R), IsNilpotent (p : R) → IsNilpotent I →
    ∀ (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (A₀ B₀ : Over (Sp (R ⧸ I))) [GrpObj A₀] [GrpObj B₀]
      (φA : A₀.left ⟶ A.left) (φB : B₀.left ⟶ B.left), IsAbelianScheme A → IsAbelianScheme B →
      IsRed I A₀ A φA → IsRed I B₀ B φB →
    ∀ (G H : PDivGroup p R) (G₀ H₀ : PDivGroup p (R ⧸ I)) (tA : G.TorsionTower A) (tB : H.TorsionTower B)
      (tA₀ : G₀.TorsionTower A₀) (tB₀ : H₀.TorsionTower B₀) (sG : SemiHom (algebraMap R (R ⧸ I)) G₀ G)
      (sH : SemiHom (algebraMap R (R ⧸ I)) H₀ H), TowerRed φA sG tA tA₀ → TowerRed φB sH tB tB₀ →
    ∀ (f₀ : A₀ ⟶ B₀) [IsMonHom f₀] (g : G ⟶ H),
      (∀ n a, sG.app n (g.app n a) = (tA₀.map tB₀ f₀).app n (sH.app n a)) →
      ∃! f : A ⟶ B, ∃ _ : IsMonHom f, φA ≫ f.left = f₀.left ≫ φB ∧ tA.map tB f = g

def LiftAny : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (I : Ideal R), IsNilpotent (p : R) → IsNilpotent I →
    ∀ (A₀ : Over (Sp (R ⧸ I))) [GrpObj A₀], IsAbelianScheme A₀ →
    ∀ (G₀ : PDivGroup p (R ⧸ I)) (t₀ : G₀.TorsionTower A₀) (G : PDivGroup p R)
      (s : SemiHom (algebraMap R (R ⧸ I)) G₀ G), IsIso s.lift →
      ∃ (A : Over (Sp R)) (_ : GrpObj A) (φ : A₀.left ⟶ A.left) (t : G.TorsionTower A),
        IsAbelianScheme A ∧ IsRed I A₀ A φ ∧ TowerRed φ s t t₀ ∧
          ∀ d : ℕ, SmoothOfRelativeDimension d A₀.hom → SmoothOfRelativeDimension d A.hom

def Lift : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (I : Ideal R), IsNilpotent (p : R) → IsNilpotent I →
    ∀ (A₀ : Over (Sp (R ⧸ I))) [GrpObj A₀], IsAbelianScheme A₀ →
    ∀ (A' : Over (Sp R)) [GrpObj A'] (φ' : A₀.left ⟶ A'.left) (L' : LB A'.left),
      IsAbelianScheme A' → IsRed I A₀ A' φ' → L'.IsLB → RelAmple A' L' →
    ∀ (G₀ : PDivGroup p (R ⧸ I)) (t₀ : G₀.TorsionTower A₀) (G : PDivGroup p R)
      (s : SemiHom (algebraMap R (R ⧸ I)) G₀ G), IsIso s.lift →
      ∃ (A : Over (Sp R)) (_ : GrpObj A) (φ : A₀.left ⟶ A.left) (t : G.TorsionTower A) (L : LB A.left),
        IsAbelianScheme A ∧ IsRed I A₀ A φ ∧ TowerRed φ s t t₀ ∧ L.IsLB ∧ RelAmple A L ∧
          ∀ d : ℕ, SmoothOfRelativeDimension d A₀.hom → SmoothOfRelativeDimension d A.hom

def SerreTate : Prop := HomLift ∧ Lift

def LiftAmple : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (I : Ideal R), IsNilpotent (p : R) → IsNilpotent I →
    ∀ (A : Over (Sp R)) [GrpObj A] (A₀ : Over (Sp (R ⧸ I))) [GrpObj A₀] (φ : A₀.left ⟶ A.left),
      IsAbelianScheme A → IsRed I A₀ A φ →
    ∀ L₀ : LB A₀.left, L₀.IsLB → RelAmple A₀ L₀ → ∃ L : LB A.left, L.IsLB ∧ RelAmple A L

def LiftProj : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (I : Ideal R), IsNilpotent (p : R) → IsNilpotent I →
    ∀ (A₀ : Over (Sp (R ⧸ I))) [GrpObj A₀] (L₀ : LB A₀.left), IsAbelianScheme A₀ → L₀.IsLB → RelAmple A₀ L₀ →
    ∀ (G₀ : PDivGroup p (R ⧸ I)) (t₀ : G₀.TorsionTower A₀) (G : PDivGroup p R)
      (s : SemiHom (algebraMap R (R ⧸ I)) G₀ G), IsIso s.lift →
      ∃ (A : Over (Sp R)) (_ : GrpObj A) (φ : A₀.left ⟶ A.left) (t : G.TorsionTower A) (L : LB A.left),
        IsAbelianScheme A ∧ IsRed I A₀ A φ ∧ TowerRed φ s t t₀ ∧ L.IsLB ∧ RelAmple A L

section Relation

variable {p : ℕ} {R : Type} [CommRing R] {I : Ideal R}

variable [Fact p.Prime]

end Relation

section Inhabitant

open GlobalTheory.SerreTateDef (Zmod4 elliptic_hyps)

example : SerreTate ↔ HomLift ∧ Lift := Iff.rfl

end Inhabitant

end GlobalTheory.SerreTate
