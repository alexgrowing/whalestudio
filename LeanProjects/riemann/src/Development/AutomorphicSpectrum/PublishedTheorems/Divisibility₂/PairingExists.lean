import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts

namespace GlobalTheory.CompanionTheory.Ar.BGS

variable {k : Type} [CommRing k] {X : Scheme.{0}}

structure IsPairing (p : X ⟶ Sp k) (T : ∀ d : ℕ, (Fin d → HermLB p) → X → ℝ) : Prop where

  iso : ∀ (d : ℕ) (L M : Fin d → HermLB p) (x : X), (∀ i, (L i).Isometric (M i)) → T d L x = T d M x

  symm : ∀ (d : ℕ) (L : Fin d → HermLB p) (e : Equiv.Perm (Fin d)) (x : X), T d (fun i => L (e i)) x = T d L x

  add : ∀ (d : ℕ) (A B : HermLB p) (L : Fin d → HermLB p) (x : X),
    T (d + 1) (Fin.cons (A.tens B) L) x = T (d + 1) (Fin.cons A L) x + T (d + 1) (Fin.cons B L) x

  vertical : ∀ (N : HermLB p) (Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z] (κ : Type)
    [Field κ] [Finite κ] [Algebra κ Γ(Z, ⊤)] (d : ℕ), topologicalKrullDim Z = d →
    T d (fun _ => N) (i (genericPoint Z)) = topSelfIntersection κ (N.B.pull i) d * Real.log (Nat.card κ)

  point : ∀ (N : HermLB p) (Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z]
    [IsLocallyNoetherian Z], CharZero Γ(Z, ⊤) → topologicalKrullDim Z = 1 →
    ∀ (r : (N.restr i).B.ι → Z.functionFieldˣ) (hr : IsRatSec (N.restr i).B r),
    T 1 (fun _ => N) (i (genericPoint Z)) = (N.restr i).curveDeg hr

  recursion : ∀ (M N : HermLB p) (Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z]
    [IsLocallyNoetherian Z], CharZero Γ(Z, ⊤) → ∀ e : ℕ, topologicalKrullDim Z = (e + 1 : ℕ) →
    ∀ (r : (M.restr i).B.ι → Z.functionFieldˣ) (hr : IsRatSec (M.restr i).B r),
    (N.restr i).ArchIntegrable (M.restr i) e hr ∧
    T (e + 1) (Fin.cons M fun _ => N) (i (genericPoint Z)) =
      ∑ᶠ z, (((M.restr i).div hr).mult z : ℝ) * T e (fun _ => N) (i z) - (N.restr i).archInt (M.restr i) e hr

def PairingExists : Prop := ∀ (X : Scheme.{0}) (p : X ⟶ Sp ℤ) (D : ℕ), IsArithVar p D → SmoothOfRelativeDimension D p →
  ∃ T, IsPairing p T

def Projection : Prop := ∀ (X Y : Scheme.{0}) (p : X ⟶ Sp ℤ) (q : Y ⟶ Sp ℤ) (D E : ℕ),
  IsArithVar p D → SmoothOfRelativeDimension D p → IsArithVar q E → SmoothOfRelativeDimension E q →
  ∀ (π : Y ⟶ X) (hπ : π ≫ p = q) (L : HermLB p) (h : X → ℝ) (h' : Y → ℝ),
    L.IsArithHeight h → (L.pull π hπ).IsArithHeight h' → ∀ (y : Y) (d : ℕ),
      topologicalKrullDim (closure ({y} : Set Y)) = d → topologicalKrullDim (closure ({π y} : Set X)) = d →
      π.residueDegree y ≠ 0 → h' y = (π.residueDegree y : ℝ) * h (π y)

def CyclePairing : Prop := PairingExists ∧ Projection

end GlobalTheory.CompanionTheory.Ar.BGS
