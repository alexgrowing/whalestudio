import Mathlib
import Formalism.PieriBlockIdeals.StatementLC
import Formalism.PieriBlockIdeals.StatementLP
import Formalism.PieriBlockIdeals.StatementLR

namespace Formalism.CohomologicalDescent.ColumnMinorsFromPieri

open Formalism.CohomologicalDescent.Symmetrization Formalism.CohomologicalDescent.BinaryFormsExample

def LemmaDSkeleton5 : Prop :=
  ∀ (O K V P : Type) (q : ℕ) [CommRing O] [Field K] [LinearOrder K] [IsStrictOrderedRing K] [Algebra O K] [AddCommGroup V]
    [Module K V] [Module O V] [IsScalarTower O K V] [DecidableEq P] [Fintype P] (S : HidaSetting K V P (Fin q))
    (B : LinearMap.BilinForm K V) (n w : ℕ) (lam2 : Fin q → ℕ) (DelL : Submodule O S.W)
    (xi : (P ⊕ Fin q → ℤ) →+ ℤ) (lam : P ⊕ Fin q → ℤ)
    (l : ℕ) (e : ℕ) (i' : ℤ), l.Prime → (∀ m : ℤ, ¬ (l : ℤ) ∣ m → IsUnit (m : O)) →
    S.w = (w : K) → (∀ b, lam2 b ≤ w) → Contra S B → Generated S →
    (∀ x y, B x y = B y x) → (∀ x, x ≠ 0 → 0 < B x x) →
    FiniteDimensional K S.W → (∀ b, ⨆ μ : K, Module.End.eigenspace (S.EW b b) μ = ⊤) →
    (∀ (v : S.W) (μ : Fin q → K), v ≠ 0 → LP.IsHW S.EW μ v → μ = fun b => (lam2 b : K)) →
    (∀ b b', ∀ u ∈ DelL, S.EW b b' u ∈ DelL) →
    (∀ (α : P) (b : Fin q), 0 ≤ xi (Pi.single (Sum.inl α) 1 - Pi.single (Sum.inr b) 1)) →
    (∀ κ, xi (lam - κ) ≤ i' → ∀ u ∈ NablaL S B DelL, (u : V) ∈ S.wt κ → (l : O) ^ e • u ∈ DelL) →
    ∀ ν, ∑ α : P, ν (Sum.inl α) + (n : ℤ) = (Fintype.card P : ℤ) * (w : ℤ) → xi (lam - ν) ≤ i' →
      ∀ v ∈ B.dualSubmodule (DeltaAll S DelL), v ∈ S.wt ν →
      (l : O) ^ (e + padicValInt l (LD.Dn (Fintype.card P) w n lam2)) • v ∈ DeltaAll S DelL ∧
        (l : O) ^ (e + padicValInt l (LD.Dn (Fintype.card P) w n lam2)) • v ∈ S.wt ν

def ColumnsInstance : Prop :=
  (⨆ tau, PathSpace ℚ (P := Unit) (fun _ _ : Fin 2 => (0 : Module.End ℚ ℚ)) 2 (fun _ => 0) tau) = ⊤ ∧
    (∃ _b : Fin 2, ∃ j < (1 : ℕ), Fintype.card Unit < LD.colLen (fun _ : Fin 2 => 0) (fun _ => 1) j) ∧
    (∃ z ∈ PathSpace ℚ (P := Unit) (fun _ _ : Fin 2 => (0 : Module.End ℚ ℚ)) 2 (fun _ => 0) (fun _ => 1),
      z ≠ 0 ∧ toSym ℚ z = 0) ∧
    ∃ z ∈ PathSpace ℚ (P := Unit) (fun _ _ : Fin 2 => (0 : Module.End ℚ ℚ)) 2 (fun _ => 0) ![2, 0], toSym ℚ z ≠ 0

def ColumnsRealOfPieriReal : Prop := LR.PieriReal → LR.ColumnsReal

def LemmaDGradedOfPieriReal : Prop := LR.PieriReal → LD.LemmaDGraded

end Formalism.CohomologicalDescent.ColumnMinorsFromPieri
