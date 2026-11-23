import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.QCoh (IsFiniteQC)
open GlobalTheory.VB

namespace GlobalTheory.IndefiniteRowSideFullHecke.DegreeAdditiveFrobenius

def IsFiniteOfDegree {C' C : Scheme.{0}} [IsIntegral C'] [IsIntegral C] (π : C' ⟶ C) (m : ℕ) :
    Prop :=
  IsFinite π ∧ π (genericPoint C') = genericPoint C ∧ π.residueDegree (genericPoint C') = m

section Clauses

variable (k : Type) [Field k] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] [IsIntegral C]

def DegAdditive : Prop :=
  ∀ S : ShortComplex C.Modules, S.ShortExact → IsFiniteQC S.X₁ → IsFiniteQC S.X₂ →
    IsFiniteQC S.X₃ → deg k S.X₂ = deg k S.X₁ + deg k S.X₃

def DegDual : Prop :=
  ∀ (E : C.Modules) (r : ℕ), IsVB E r → deg k (dual E) = -deg k E

def DegDet : Prop :=
  ∀ (E : C.Modules) (r : ℕ), IsVB E r → degLB k (det E r) = deg k E

def DegLeSat : Prop :=
  ∀ (E ξ : C.Modules) (r : ℕ) (i : ξ ⟶ E), IsVB E r → IsCohSub i → deg k ξ ≤ deg k (sat i)

def SubDegBounded : Prop :=
  ∀ (E : C.Modules) (r : ℕ), IsVB E r →
    BddAbove (subDegs k E) ∧ ∃ P : ℤ, IsMaxSubDeg k E P ∧ 0 ≤ P

variable {C} in

def PullbackRules {C' : Scheme.{0}} [Algebra k Γ(C', ⊤)] [IsIntegral C'] (π : C' ⟶ C) (m : ℕ) :
    Prop :=
  Flat π ∧
  (∀ (E : C.Modules) (r : ℕ), IsVB E r →
    deg k ((Scheme.Modules.pullback π).obj E) = (m : ℤ) * deg k E) ∧
  (∀ (E ξ : C.Modules) (r : ℕ) (i : ξ ⟶ E), IsVB E r → IsCohSub i →
    IsCohSub ((Scheme.Modules.pullback π).map i) ∧
      deg k ((Scheme.Modules.pullback π).obj ξ) = (m : ℤ) * deg k ξ) ∧
  (∀ (E : C.Modules) (r : ℕ) (P P' : ℤ), IsVB E r → IsMaxSubDeg k E P →
    IsMaxSubDeg k ((Scheme.Modules.pullback π).obj E) P' → (m : ℤ) * P ≤ P')

def CoverRules : Prop :=
  ∀ (C' : Scheme.{0}) [Algebra k Γ(C', ⊤)] [IsIntegral C'] (π : C' ⟶ C) (m : ℕ),
    IsSmoothProjCurve k C' → π ≫ strHom k C = strHom k C' → IsFiniteOfDegree π m →
      PullbackRules k π m

def FrobeniusRules : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] [CharP k p],
    IsFiniteOfDegree (frob C p (natCast_eq_zero C p k)) p ∧
      PullbackRules k (frob C p (natCast_eq_zero C p k)) p

end Clauses

def CurveDegrees : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] [IsIntegral C],
    IsSmoothProjCurve k C →
      DegAdditive k C ∧ DegDual k C ∧ DegDet k C ∧ DegLeSat k C ∧ CoverRules k C ∧
        FrobeniusRules k C ∧ SubDegBounded k C

theorem IsFiniteOfDegree.unique {C' C : Scheme.{0}} [IsIntegral C'] [IsIntegral C] {π : C' ⟶ C}
    {m n : ℕ} (h : IsFiniteOfDegree π m) (h' : IsFiniteOfDegree π n) : m = n :=
  h.2.2.symm.trans h'.2.2

open GlobalTheory.ProjSpace GlobalTheory.ProjCoh in
attribute [local instance] MvPolynomial.gradedAlgebra in

example (H : CurveDegrees) (k : Type) [Field k] [IsAlgClosed k] [Fact (Nat.Prime 3)] [CharP k 3] :
    deg k ((frobPull 3 (natCast_eq_zero (PSpace k 1) 3 k)).obj (sheafO k 1 2)) = 6 := by
  have h := ((H k (PSpace k 1) (isSmoothProjCurve_line k)).2.2.2.2.2.1 3).2.2.1 _ 1
    (isVB_sheafO k 2)
  rw [deg_sheafO] at h
  exact h

end GlobalTheory.IndefiniteRowSideFullHecke.DegreeAdditiveFrobenius
