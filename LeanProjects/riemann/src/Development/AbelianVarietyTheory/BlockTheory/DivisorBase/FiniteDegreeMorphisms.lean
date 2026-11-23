import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.QCoh (IsFiniteQC)
open GlobalTheory.VB

namespace GlobalTheory.IndefiniteRowSideFullHecke.FiniteDegreeMorphisms

structure IsFiniteOfDegree {C' C : Scheme.{0}} [IsIntegral C] (π : C' ⟶ C) (m : ℕ) : Prop where

  isFinite : IsFinite π

  finrank_eq : π.finrank (genericPoint C) = m

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
  ∀ (E : C.Modules) (r : ℕ), IsVB E r → ∀ (G : C.Modules) (i : G ⟶ E), IsCohSub i →
    deg k G ≤ deg k (sat i)

def MaxSubDegExists : Prop :=
  ∀ (E : C.Modules) (r : ℕ), IsVB E r →
    BddAbove (subDegs k E) ∧ ∃ P : ℤ, IsMaxSubDeg k E P

variable {C} in

def ScalesDeg {C' : Scheme.{0}} [Algebra k Γ(C', ⊤)] [IsIntegral C'] (π : C' ⟶ C) (m : ℕ) : Prop :=
  ∀ (E : C.Modules) (r : ℕ), IsVB E r →
    deg k ((Scheme.Modules.pullback π).obj E) = m * deg k E ∧
    ∀ (G : C.Modules) (i : G ⟶ E), IsCohSub i →
      IsCohSub ((Scheme.Modules.pullback π).map i) ∧
      deg k ((Scheme.Modules.pullback π).obj G) = m * deg k G

def DegCover : Prop :=
  ∀ (C' : Scheme.{0}) [Algebra k Γ(C', ⊤)] [IsIntegral C'], IsSmoothProjCurve k C' →
    ∀ (π : C' ⟶ C) (m : ℕ), π ≫ strHom k C = strHom k C' → IsFiniteOfDegree π m →
      Flat π ∧ ScalesDeg k π m

def DegFrob (p : ℕ) [Fact p.Prime] [CharP k p] : Prop :=
  IsFiniteOfDegree (frob C p (natCast_eq_zero C p k)) p ∧
    Flat (frob C p (natCast_eq_zero C p k)) ∧ ScalesDeg k (frob C p (natCast_eq_zero C p k)) p

end Clauses

def CurveDegrees : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [IsAlgClosed k] [CharP k p]
    (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] [IsIntegral C], IsSmoothProjCurve k C →
    DegAdditive k C ∧ DegDual k C ∧ DegDet k C ∧ DegLeSat k C ∧ DegCover k C ∧ DegFrob k C p ∧
      MaxSubDegExists k C

section Basic₂

open ProjSpace ProjCoh

variable {k : Type} [Field k] {C C' : Scheme.{0}} [Algebra k Γ(C, ⊤)] [IsIntegral C]
  [Algebra k Γ(C', ⊤)] [IsIntegral C']

theorem ScalesDeg.mul_le {π : C' ⟶ C} {m : ℕ} (h : ScalesDeg k π m) {E : C.Modules} {r : ℕ}
    (hE : IsVB E r) {P P' : ℤ} (hP : IsMaxSubDeg k E P)
    (hP' : IsMaxSubDeg k ((Scheme.Modules.pullback π).obj E) P') : m * P ≤ P' := by
  obtain ⟨G, i, hi, rfl⟩ := hP.exists_isCohSub
  obtain ⟨h₁, h₂⟩ := (h E r hE).2 G i hi
  rw [← h₂]
  exact hP'.2 h₁.deg_mem

example [Fact (Nat.Prime 3)] : IsSmoothProjCurve (AlgebraicClosure (ZMod 3))
    (PSpace (AlgebraicClosure (ZMod 3)) 1) := isSmoothProjCurve_line _

end Basic₂

end GlobalTheory.IndefiniteRowSideFullHecke.FiniteDegreeMorphisms
