import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegProd
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.ActFin

def QHyp {S : Scheme.{0}} (A : Over S) [GrpObj A] (Q : LB (A ⊗ A).left) : Prop :=
  IsAbelianScheme A ∧ Q.IsLB ∧ (∃ t : (Q.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) ∧
    (∃ t : (Q.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) ∧
    LBIso Q (Q.pull (lift (snd A A) (fst A A)).left) ∧ Out.RelAmple A (Q.pull (lift (𝟙 A) (𝟙 A)).left)

def formLB {S : Scheme.{0}} (A : Over S) (Q : LB (A ⊗ A).left) {G : Over S} {r : ℕ} (pr : Fin r → (G ⟶ A))
    (W : Matrix (Fin r) (Fin r) ℤ) : LB G.left :=
  LB.LinComb Q (K := Fin r × Fin r) (fun uv => (lift (pr uv.1) (pr uv.2)).left) (fun uv => W uv.1 uv.2)

def diagPow {S : Scheme.{0}} (A : Over S) (Q : LB (A ⊗ A).left) (d : ℤ) : LB A.left :=
  LB.LinComb Q (K := Fin 1) (fun _ => (lift (𝟙 A) (𝟙 A)).left) (fun _ => d)

def sqMap {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} (f : S' ⟶ S) (φ : G'.left ⟶ G.left)
    (w : φ ≫ G.hom = G'.hom ≫ f) : (G' ⊗ G').left ⟶ (G ⊗ G).left :=
  pullback.lift ((fst G' G').left ≫ φ) ((snd G' G').left ≫ φ) (by
    rw [Category.assoc, Category.assoc, w, ← Category.assoc, ← Category.assoc, Over.w (fst G' G'), Over.w (snd G' G')])

theorem isSquare_sqMap {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} (f : S' ⟶ S) (φ : G'.left ⟶ G.left)
    (w : φ ≫ G.hom = G'.hom ≫ f) : IsSquare φ (sqMap f φ w) :=
  ⟨pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩

theorem isSquare_comp {S S' S'' : Scheme.{0}} {G : Over S} {G' : Over S'} {G'' : Over S''} {φ : G'.left ⟶ G.left}
    {φ₂ : (G' ⊗ G').left ⟶ (G ⊗ G).left} {φ' : G''.left ⟶ G'.left} {φ₂' : (G'' ⊗ G'').left ⟶ (G' ⊗ G').left}
    (h' : IsSquare φ' φ₂') (h : IsSquare φ φ₂) : IsSquare (φ' ≫ φ) (φ₂' ≫ φ₂) :=
  ⟨by rw [Category.assoc, h.1, ← Category.assoc, h'.1, Category.assoc],
   by rw [Category.assoc, h.2, ← Category.assoc, h'.2, Category.assoc]⟩

theorem isMonHom_prodPow {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {r : ℕ} (f : Fin r → (A ⟶ A))
    (hf : ∀ k, IsMonHom (f k)) (c : Fin r → ℤ) : IsMonHom (∏ k, f k ^ c k) :=
  Finset.prod_induction _ (fun x => IsMonHom x) (fun a b ha hb => by
    haveI := ha; haveI := hb; exact GlobalTheory.Serre.isMonHom_mul a b) GlobalTheory.Serre.isMonHom_one fun k _ => by
    haveI := hf k; exact GlobalTheory.Serre.isMonHom_zpow _ _

theorem powext {S : Scheme.{0}} (A : Over S) (r : ℕ) {X : Scheme.{0}} (a b : X ⟶ (Out.powObj A r).left)
    (h0 : a ≫ (Out.powObj A r).hom = b ≫ (Out.powObj A r).hom)
    (h : ∀ k, a ≫ (Out.powPr A k).left = b ≫ (Out.powPr A k).left) : a = b := by
  have := (Out.powIsLimit A r).hom_ext (W := Over.mk (b ≫ (Out.powObj A r).hom)) (f := Over.homMk a h0)
    (f' := Over.homMk b rfl) (fun ⟨k⟩ => Over.OverMorphism.ext (by simpa using h k))
  exact congrArg (fun m => m.left) this

end GlobalTheory.ActFin
