import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InvariantOfTsupport
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeUnipotentExistsResidueCardPowMemNhds

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SBUnif

theorem uniform : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (Ψ : Matrix n n' k → ℂ), Ψ ∈ SB (Matrix n n' k) → ∃ N : ℕ, 0 < N ∧ (∀ X Y : Matrix n n' k, (∀ i j, Y i j ∈ 𝒪[k]) → Ψ (X + (N : k) • Y) = Ψ X) ∧ ∀ X, Ψ X ≠ 0 → ∀ i j, (N : k) * X i j ∈ 𝒪[k] := by
  intro k _ _ _ _ n n' _ _ _ _ Ψ hΨ
  classical
  obtain ⟨a, ha⟩ := GlobalTheory.LocMod.Inhab.exists_box_subset (GlobalTheory.LocMod.Inhab.eventually_invariant hΨ)
  have hinv : ∀ X u, u ∈ GlobalTheory.LocMod.Inhab.box n n' a → Ψ (X + u) = Ψ X := fun X u hu =>
    GlobalTheory.LocMod.Inhab.invariant_of_tsupport (K := GlobalTheory.LocMod.Inhab.box n n' a) (fun u hu => ha u hu) u hu X
  obtain ⟨R, hR⟩ := GlobalTheory.LocMod.Inhab.exists_cosets hΨ a
  let F : Finset k := insert (a : k) ((R ×ˢ (Finset.univ ×ˢ Finset.univ)).image fun x => x.1 x.2.1 x.2.2)
  obtain ⟨b, -, hb⟩ := F.exists_max_image (fun x => valuation k x) ⟨_, Finset.mem_insert_self _ _⟩
  have hab : valuation k (a : k) ≤ valuation k b := hb _ (Finset.mem_insert_self _ _)
  have ha0 : valuation k (a : k) ≠ 0 := by simp
  have hb0 : valuation k b ≠ 0 := fun h => ha0 (le_antisymm (h ▸ hab) zero_le')
  have hsupp : ∀ X, Ψ X ≠ 0 → ∀ i j, valuation k (X i j) ≤ valuation k b := by
    intro X hX i j
    obtain ⟨r, hr, hXr⟩ := hR X hX
    have h1 : valuation k ((X - r) i j) ≤ valuation k (a : k) := hXr i j
    have h2 : valuation k (r i j) ≤ valuation k b :=
      hb _ (Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨(r, i, j), by simp [hr], rfl⟩))
    have e : X i j = r i j + (X - r) i j := by simp
    rw [e]
    exact Valuation.map_add_le _ h2 (h1.trans hab)
  have hq := GlobalTheory.RootEx.UnipPow.valuation_resCard_lt_one (k := k)
  obtain ⟨e₁, he₁⟩ := exists_pow_lt₀ hq (Units.mk0 _ ha0)
  obtain ⟨e₂, he₂⟩ := exists_pow_lt₀ hq (Units.mk0 _ (inv_ne_zero hb0))
  have hpos : 0 < resCard k := Nat.card_pos
  refine ⟨resCard k ^ (e₁ + e₂), pow_pos hpos _, ?_, ?_⟩
  · intro X Y hY
    refine hinv X _ fun r q => ?_
    rw [Matrix.smul_apply, smul_eq_mul, map_mul, Nat.cast_pow, map_pow]
    have hY' : valuation k (Y r q) ≤ 1 := hY r q
    calc valuation k (resCard k : k) ^ (e₁ + e₂) * valuation k (Y r q)
        ≤ valuation k (resCard k : k) ^ e₁ * 1 :=
          mul_le_mul' (pow_le_pow_right_of_le_one' hq.le (Nat.le_add_right _ _)) hY'
      _ ≤ valuation k (a : k) := by rw [mul_one]; exact he₁.le
  · intro X hX i j
    show valuation k _ ≤ 1
    rw [map_mul, Nat.cast_pow, map_pow]
    calc valuation k (resCard k : k) ^ (e₁ + e₂) * valuation k (X i j)
        ≤ (valuation k b)⁻¹ * valuation k b :=
          mul_le_mul' ((pow_le_pow_right_of_le_one' hq.le (Nat.le_add_left _ _)).trans he₂.le) (hsupp X hX i j)
      _ = 1 := inv_mul_cancel₀ hb0

end GlobalTheory.SBUnif
