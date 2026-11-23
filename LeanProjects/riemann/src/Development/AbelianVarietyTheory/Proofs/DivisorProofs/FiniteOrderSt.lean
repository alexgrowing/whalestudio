import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EffOfSec
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsOddNeZero

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AmpleRigid

open GlobalTheory.CechPic

def ConstSt : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A →
    ∀ (L : LB A.left) (hL : L.IsLB), Out.RelAmple A L → ∀ m : Pic A.left, ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t →
      ∀ ψ : A ⟶ A, IsMonHom ψ → GlobalTheory.EffBound.Eff (m - t • pull ψ.left (cls L hL)) → ψ = 1

def CubeSt : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A →
    ∀ (L : LB A.left), L.IsLB → Out.RelAmple A L → ∀ (c : Pic A.left) (x y z : A ⟶ A),
      pull (x * y * z).left c + pull x.left c + pull y.left c + pull z.left c =
        pull (x * y).left c + pull (x * z).left c + pull (y * z).left c + pull (1 : A ⟶ A).left c

def FiniteOrderSt : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A →
    ∀ (L : LB A.left) (hL : L.IsLB), Out.RelAmple A L → ∀ σ : A ≅ A, IsMonHom σ.hom →
      pull σ.hom.left (cls L hL) = cls L hL → ∃ m : ℕ, m ≠ 0 ∧ (GlobalTheory.SerreField.iter σ m).hom = 𝟙 A

def SeparatedSt : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A →
    ∀ (L : LB A.left), L.IsLB → Out.RelAmple A L → ∀ q : ℕ, 2 ≤ q → ∀ u : A ⟶ A,
      (∀ k : ℕ, ∃ ψ : A ⟶ A, IsMonHom ψ ∧ u = ψ ^ (q ^ k)) → u = 1

def SerreAmpleSt : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A →
    ∀ (L : LB A.left) (hL : L.IsLB), Out.RelAmple A L → ∀ N : ℕ, 3 ≤ N → (N : K) ≠ 0 →
      ∀ σ : A ≅ A, IsMonHom σ.hom → pull σ.hom.left (cls L hL) = cls L hL →
      (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ Sp K) (x : Over.mk t ⟶ A), x ^ N = 1 → x ≫ σ.hom = x) →
      σ.hom = 𝟙 A

open GlobalTheory.RealMult in

def LevelRigidSt : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (N : ℕ), 3 ≤ N →
    ∀ (R : Type) [CommRing R], IsUnit (N : R) → ∀ (X : Obj F 𝔠 (Sp R)) (β : X.Level N)
      (g : X.A.left ⟶ X.A.left), X.IsPullBy X (𝟙 _) g → (∀ i, (β.pt i).left ≫ g = (β.pt i).left) → g = 𝟙 _

end GlobalTheory.AmpleRigid
