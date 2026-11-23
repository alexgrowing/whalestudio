import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds

open GlobalTheory.BK PowerSeries

def C₀ : ℕ := 40

structure Bounds (l e : ℕ) (Sig : Finset (ZMod e)) (U : Finset ℤ) (N η H : ℕ) : Prop where

  frob_mem : ∀ c ∈ Sig, (l : ZMod e) * c ∈ Sig

  zero_mem_Sig : (0 : ZMod e) ∈ Sig
  card_Sig : Sig.card ≤ N
  two_le : 2 ≤ N

  range_U : ∀ i ∈ U, -(η : ℤ) ≤ i ∧ i ≤ (H : ℤ)
  zero_mem_U : (0 : ℤ) ∈ U
  card_U : U.card ≤ N + 1
  one_le : 1 ≤ η
  lt : η < H

  large : C₀ * (H * N ^ 2 + N ^ 3) < l

def rho (l : ℕ) {e : ℕ} (Sig : Finset (ZMod e)) (N : ℕ) : ℕ := 2 * (N - 1) * maxPeriod l Sig

def KillsCoker {V₁ V₂ : Type} [AddCommGroup V₂] (f : V₁ → V₂) (n : ℕ) (W₁ : Set V₁) (W₂ : Set V₂) : Prop :=
  ∀ y ∈ W₂, ∃ x ∈ W₁, f x = n • y

section

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] {η H : ℕ}

def KillsAll {D₁ : BKDat O K l e a ι η H} {D₂ : BKDat O K l e a κ η H} (F : BKHom D₁ D₂) (n : ℕ) :
    Prop :=
  KillsCoker F.app n D₁.L D₂.L ∧
  KillsCoker F.app n D₁.M D₂.M ∧
  KillsCoker F.app n (D₁.EM η) (D₂.EM η) ∧
  KillsCoker F.app n D₁.Minv D₂.Minv ∧
  KillsCoker F.app n D₁.Y D₂.Y ∧
  KillsCoker F.app n D₁.Y' D₂.Y'

omit [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] in

theorem killsCoker_M_iff {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} (F : Hom P Q) (n : ℕ) :
    KillsCoker F.app n P.M Q.M ↔ ∀ q : F.coker, n • q = 0 := by
  constructor
  · intro h q
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨x, hx, hxy⟩ := h y y.2
    rw [← Submodule.mkQ_apply, ← map_nsmul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact ⟨x, hx, hxy⟩
  · intro h y hy
    have h1 := h (Submodule.Quotient.mk ⟨y, hy⟩)
    rw [← Submodule.mkQ_apply, ← map_nsmul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h1
    exact h1

end

def Stmt : Prop :=
  ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
    (l e a : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a]
    (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (Sig : Finset (ZMod e)) (U : Finset ℤ) (N η H : ℕ), Bounds l e Sig U N η H →
    ∀ (D₁ : BKDat O K l e a ι η H) (D₂ : BKDat O K l e a κ η H),
      D₁.IsOfType (Sig : Set (ZMod e)) (U : Set ℤ) → (∀ τ, D₂.desc.chars τ ⊆ (Sig : Set (ZMod e))) →
      ∀ F : BKHom D₁ D₂, IsFiniteLength (A O K) F.coker →
        KillsAll F (l ^ rho l Sig N)

example (l e N : ℕ) : rho l ({0} : Finset (ZMod e)) N = 2 * (N - 1) := by
  simp [rho, maxPeriod, frobPeriod, Function.minimalPeriod_eq_one_iff_isFixedPt.2
    (show Function.IsFixedPt (fun x => (l : ZMod e) * x) 0 from mul_zero _)]

end GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds
