import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.VB
open GlobalTheory.QCoh (freeModule)

namespace GlobalTheory.IndefiniteRowSideFullHecke.FrobeniusTwistEigen

def IsExtension {X : Scheme.{0}} (A H B : X.Modules) : Prop :=
  ∃ (i : A ⟶ H) (q : H ⟶ B) (w : i ≫ q = 0), (ShortComplex.mk i q w).ShortExact

abbrev frobTwist (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] {X : Scheme.{0}}
    [Algebra k Γ(X, ⊤)] (M : X.Modules) : X.Modules :=
  (frobPull p (natCast_eq_zero X p k)).obj M

def SlopeInequality : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [IsAlgClosed k] [CharP k p]
    (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] [IsIntegral C], IsSmoothProjCurve k C →
    ∀ (L H : C.Modules) (g : ℕ), IsVB L g → IsVB H (2 * g) →
      IsExtension (dual L) H L →
      (∃ v : frobTwist p k L ⟶ H, Mono v) →
      ∀ P : ℤ, IsMaxSubDeg k L P → (p : ℤ) * P ≤ -deg k L + 2 * P

def EigenDegrees : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [IsAlgClosed k] [CharP k p]
    (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] [IsIntegral C], IsSmoothProjCurve k C →
    ∀ (ι : Type) [Fintype ι] (φ : Equiv.Perm ι) (c : ι → ι), Function.Involutive c →
    ∀ (L H : ι → C.Modules) (m n : ι → ℕ), (∀ τ, IsVB (L τ) (m τ)) → (∀ τ, IsVB (H τ) (n τ)) →
      (∀ τ, IsExtension (dual (L (c τ))) (H τ) (L τ)) →
      (∀ τ, IsExtension (frobTwist p k (L τ)) (H (φ τ)) (frobTwist p k (dual (L (c τ))))) →
      (∀ τ, deg k (H τ) = 0) ∧ (∀ τ, deg k (L τ) = deg k (L (c τ))) ∧
        ∀ (M : C.Modules), Nonempty (M ≅ ∐ L) →
          ∀ Ψ : Finset ι, (∀ τ, τ ∈ Ψ ↔ c τ ∉ Ψ) →
            2 * ∑ τ ∈ Ψ, deg k (dual (L τ)) = -deg k M

def SlopeAndEigenDegrees : Prop := SlopeInequality ∧ EigenDegrees

end GlobalTheory.IndefiniteRowSideFullHecke.FrobeniusTwistEigen
