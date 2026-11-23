import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleSignatures

open GlobalTheory.BK PowerSeries

structure Admissible (l e N η H : ℕ) (Sig : Finset (ZMod e)) (U : Finset ℤ) : Prop where
  frob_mem : ∀ c ∈ Sig, (l : ZMod e) * c ∈ Sig
  zero_mem_Sig : (0 : ZMod e) ∈ Sig
  card_Sig : Sig.card ≤ N
  two_le : 2 ≤ N
  range_U : ∀ i ∈ U, -(η : ℤ) ≤ i ∧ i ≤ (H : ℤ)
  zero_mem_U : (0 : ℤ) ∈ U
  card_U : U.card ≤ N + 1
  one_le : 1 ≤ η
  lt : η < H
  large : 40 * (H * N ^ 2 + N ^ 3) < l

def cOne (l : ℕ) {e : ℕ} (η : ℕ) (Sig : Finset (ZMod e)) : ℕ := η * (maxPeriod l Sig + 1)

def ZetaBound : Prop :=
  ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
    (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K]
    [NeZero e] [NeZero a] [TameDescentExponentData K l e a]
    (N η H : ℕ) (Sig : Finset (ZMod e)) (U : Finset ℤ), Admissible l e N η H Sig U →
    ∀ D : BKDat O K l e a ι η H, D.IsOfType (Sig : Set (ZMod e)) (U : Set ℤ) →
    ∀ y' ∈ D.Y', ∀ m ∈ D.Minv, D.Mon (y' + D.phi m) = 0 →
      (l : K) ^ cOne l η Sig • D.zeta (y' + D.phi m) ∈ D.MM

section Basic₂

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [Fact l.Prime]
  [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] {η H : ℕ}
  {D : BKDat O K l e a ι η H}

omit [NeZero e]

theorem add_phi_mem_Y {y' m : Vec K a ι} (hy : y' ∈ D.Y') (hm : m ∈ D.Minv) :
    y' + D.phi m ∈ D.Y :=
  add_mem (D.desc.Y'_le_Y η hy)
    ⟨D.upper _ (D.phi_mem_L hm.1), fun g => by rw [D.desc.act_phi, hm.2 g]⟩

end Basic₂

end GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleSignatures
