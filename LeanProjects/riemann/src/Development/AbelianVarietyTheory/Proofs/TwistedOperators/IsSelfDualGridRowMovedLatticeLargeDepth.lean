import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TiltSc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiDiagonalEpsilonGramMulVec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StaircaseIdealConjugateInverse
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemMulInvIff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open scoped nonZeroDivisors

namespace GlobalTheory.RowShape

variable {D : D7}

theorem mem_spanSingleton_mul_iff {s x : D.host.E} (hs : s ≠ 0) (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) :
    x ∈ FractionalIdeal.spanSingleton _ s * I ↔ x * s⁻¹ ∈ I := by
  rw [FractionalIdeal.mem_singleton_mul]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rwa [mul_comm, ← mul_assoc, inv_mul_cancel₀ hs, one_mul]
  · intro h
    exact ⟨x * s⁻¹, h, by rw [mul_comm, mul_assoc, inv_mul_cancel₀ hs, mul_one]⟩

theorem tiltSc_ne_zero (j : ℕ) (p : Fin (D.R.m - 1 - j)) : tiltSc D j p ≠ 0 := by
  unfold tiltSc
  split_ifs
  · exact inv_ne_zero (pow_ne_zero _ cmHost_imaginaryGenerator_ne_zero)
  · exact star_ne_zero.2 (pow_ne_zero _ cmHost_imaginaryGenerator_ne_zero)
  · exact one_ne_zero

theorem tiltSc_mul_star_rev (j : ℕ) (p : Fin (D.R.m - 1 - j)) : tiltSc D j p * star (tiltSc D j p.rev) = 1 := by
  have hx : D.host.xi0 ≠ 0 := cmHost_imaginaryGenerator_ne_zero
  obtain ⟨a, ha⟩ := D.R.m_even
  have hp := p.2
  unfold tiltSc
  by_cases hj : Odd j
  · obtain ⟨b, hb⟩ := hj
    have hj' : Odd j := ⟨b, hb⟩
    rw [if_pos hj', if_pos hj', Fin.val_rev]
    by_cases h1 : 2 * p.1 < D.R.m - 1 - j
    · rw [if_pos h1, if_neg (by omega)]
      have e : D.R.m - 1 - j - 1 - (D.R.m - 1 - j - (p.1 + 1)) = p.1 := by omega
      rw [e, star_star, inv_mul_cancel₀ (pow_ne_zero _ hx)]
    · rw [if_neg h1, if_pos (by omega)]
      have e : D.R.m - 1 - j - (p.1 + 1) = D.R.m - 1 - j - 1 - p.1 := by omega
      rw [e, star_inv₀, mul_inv_cancel₀ (star_ne_zero.2 (pow_ne_zero _ hx))]
  · rw [if_neg hj, if_neg hj, star_one, one_mul]

theorem rowId_ne_zero_and_dual (j : ℕ) (p : Fin (D.R.m - 1 - j)) :
    rowId D j p ≠ 0 ∧ ∀ x, x ∈ rowId D j p.rev ↔ star x ∈ (rowId D j p)⁻¹ := by
  obtain ⟨hA, hconj⟩ := (GlobalTheory.ChiGrid.StairConj.conj_AA_and_stA D).1
  obtain ⟨h0, hd⟩ := GlobalTheory.ChiGrid.stairId_ne_zero_and_mem_rev_iff D _ _ hA hconj (D.R.m - 1 - j) p
  have hs := tiltSc_ne_zero (D := D) j p
  have hs' := tiltSc_ne_zero (D := D) j p.rev
  refine ⟨mul_ne_zero (FractionalIdeal.spanSingleton_ne_zero_iff.2 hs) h0, fun x => ?_⟩
  unfold rowId
  rw [mul_inv, FractionalIdeal.spanSingleton_inv, mem_spanSingleton_mul_iff hs', mem_spanSingleton_mul_iff (inv_ne_zero hs),
    inv_inv, hd, star_mul', star_inv₀]
  have e : (star (tiltSc D j p.rev))⁻¹ = tiltSc D j p := by
    exact inv_eq_of_mul_eq_one_left (tiltSc_mul_star_rev j p)
  rw [e]

variable {T : Type} {L : LevCh D T} {sc : Consts}

theorem isSelfDualC_rowN (G : GridData L sc) (j : ℕ) (hj : j ≤ D.R.m) : IsSelfDualC _ (rowN G j) := by
  unfold rowN
  split_ifs with h
  · refine GlobalTheory.ChiGrid.SumDual.isSelfDualC_lat D _ _ _ _ (G.rowDec j h) _ _ (Or.inr rfl)
      (G.isV (X := .top j) hj (fun _ h' => by cases h')).sd (fun p => (rowId_ne_zero_and_dual j p).1)
      (fun p x => (rowId_ne_zero_and_dual j p).2 x)
  · exact (G.isV (X := .grid D.R.m j) ⟨le_rfl, hj⟩ (fun _ h' => by
      have := D.R.two_le_m
      injection h' with h1; omega)).sd

end GlobalTheory.RowShape

theorem GlobalTheory.RowShape.big_isSelfDualC_rowN :
    Big fun {D} {Γ} _ _ {Pl0 T} {A} {Ks} _ _ _ {R} ch => ∀ j, j ≤ D.R.m → IsSelfDualC _ (GlobalTheory.RowShape.rowN ch.G j) :=
  ⟨0, fun _ _ _ => ⟨0, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ch _ _ j hj => GlobalTheory.RowShape.isSelfDualC_rowN ch.G j hj⟩⟩

end
