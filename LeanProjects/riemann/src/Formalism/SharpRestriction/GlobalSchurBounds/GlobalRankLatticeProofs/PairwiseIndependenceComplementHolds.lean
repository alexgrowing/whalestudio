import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.ConclusionR7abs
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.BranchingInterlacingPairs

noncomputable section

namespace Formalism.MainNotions.UnusedSlot33

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory

namespace BernoulliMarginals

variable {α : Type*} [Fintype α] [DecidableEq α]

end BernoulliMarginals

namespace UpperTriangularReduction

open Matrix Filter Topology Polynomial

section UT

variable {k : ℕ} {S : Type*} [CommRing S]

def UT (B : Matrix (Fin k) (Fin k) S) : Prop := B.BlockTriangular id ∧ ∀ i, B i i = 1

theorem diag_mul {A B : Matrix (Fin k) (Fin k) S} (hA : A.BlockTriangular id)
    (hB : B.BlockTriangular id) (i : Fin k) : (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro j _ hji
    rcases lt_or_gt_of_ne hji with h | h
    · rw [hA h, zero_mul]
    · rw [hB h, mul_zero]
  · simp

theorem UT.mul {A B : Matrix (Fin k) (Fin k) S} (hA : UT A) (hB : UT B) : UT (A * B) :=
  ⟨hA.1.mul hB.1, fun i => by rw [diag_mul hA.1 hB.1, hA.2, hB.2, one_mul]⟩

theorem UT.one : UT (1 : Matrix (Fin k) (Fin k) S) :=
  ⟨Matrix.blockTriangular_one, fun i => Matrix.one_apply_eq i⟩

def Uk (k : ℕ) (S : Type*) [CommRing S] : Subgroup (GL (Fin k) S) where
  carrier := {M | UT (M : Matrix (Fin k) (Fin k) S)}
  one_mem' := UT.one
  mul_mem' := fun {a b} ha hb => by
    show UT ((a * b : GL (Fin k) S) : Matrix (Fin k) (Fin k) S)
    rw [Units.val_mul]
    exact UT.mul ha hb
  inv_mem' := fun {a} ha => by
    show UT ((a⁻¹ : GL (Fin k) S) : Matrix (Fin k) (Fin k) S)
    have ha' : UT (a : Matrix (Fin k) (Fin k) S) := ha
    have : Invertible (a : Matrix (Fin k) (Fin k) S) := Units.invertible a
    have ht : ((a⁻¹ : GL (Fin k) S) : Matrix (Fin k) (Fin k) S).BlockTriangular id := by
      rw [Matrix.coe_units_inv]
      exact Matrix.blockTriangular_inv_of_blockTriangular ha'.1
    refine ⟨ht, fun i => ?_⟩
    have h1 := diag_mul ha'.1 ht i
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_apply_eq, ha'.2, one_mul] at h1
    exact h1.symm

theorem UT.nilp {B : Matrix (Fin k) (Fin k) S} (hB : UT B) : (B - 1) ^ k = 0 := by
  have h := Matrix.aeval_self_charpoly B
  rw [Matrix.charpoly_of_isUpperTriangular B hB.1] at h
  simpa [hB.2] using h

end UT

variable (g k : ℕ) [Fact g.Prime]

theorem red_pow {B : Matrix (Fin k) (Fin k) (ZMod g)} (hB : UT B) : B ^ g ^ k = 1 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact Subsingleton.elim _ _
  · have : Nonempty (Fin k) := Fin.pos_iff_nonempty.1 hk
    have : CharP (Matrix (Fin k) (Fin k) (ZMod g)) g := Matrix.charP g
    have h1 : (B - 1) ^ g ^ k = B ^ g ^ k - 1 ^ g ^ k :=
      sub_pow_char_pow_of_commute g k (Commute.one_right B)
    have h2 : (B - 1) ^ g ^ k = 0 :=
      pow_eq_zero_of_le (Nat.lt_pow_self (Fact.out : g.Prime).one_lt).le hB.nilp
    rw [h2, one_pow] at h1
    exact (sub_eq_zero.1 h1.symm)

theorem lift_one (C : Matrix (Fin k) (Fin k) ℤ_[g])
    (hC : C.map (PadicInt.toZMod (p := g)) = 1) :
    ∃ Y : Matrix (Fin k) (Fin k) ℤ_[g], C = 1 + (g : Matrix (Fin k) (Fin k) ℤ_[g]) * Y := by
  have h : ∀ i j, ∃ y : ℤ_[g], (C - 1) i j = (g : ℤ_[g]) * y := by
    intro i j
    have h0 : PadicInt.toZMod ((C - 1) i j) = 0 := by
      have h1 : (PadicInt.toZMod (p := g)).mapMatrix (C - 1) = 0 := by
        rw [map_sub, map_one, RingHom.mapMatrix_apply, hC, sub_self]
      have h2 := congrFun (congrFun h1 i) j
      simpa [RingHom.mapMatrix_apply] using h2
    rw [← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
      Ideal.mem_span_singleton] at h0
    exact h0
  choose Y hY using h
  refine ⟨Matrix.of Y, ?_⟩
  ext i j
  have h1 : ((g : Matrix (Fin k) (Fin k) ℤ_[g]) * Matrix.of Y) i j = (g : ℤ_[g]) * Y i j := by
    rw [← nsmul_eq_mul, Matrix.smul_apply, nsmul_eq_mul, Matrix.of_apply]
  rw [Matrix.add_apply, h1, ← hY i j, Matrix.sub_apply]
  ring

theorem pow_one_add (Y : Matrix (Fin k) (Fin k) ℤ_[g]) (b : ℕ) :
    ∃ Z : Matrix (Fin k) (Fin k) ℤ_[g],
      (1 + (g : Matrix (Fin k) (Fin k) ℤ_[g]) * Y) ^ g ^ b = 1 + (g ^ (b + 1)) • Z := by
  have hd : ((g : ℕ) : ℤ_[g][X]) ^ (b + 1) ∣
      (1 + ((g : ℕ) : ℤ_[g][X]) * X) ^ g ^ b - 1 ^ g ^ b :=
    dvd_sub_pow_of_dvd_sub ⟨X, by ring⟩ b
  obtain ⟨Q, hQ⟩ := hd
  refine ⟨aeval Y Q, ?_⟩
  have h := congrArg (aeval Y) hQ
  simp only [map_sub, map_pow, map_add, map_one, map_mul, map_natCast, aeval_X] at h
  rw [one_pow, sub_eq_iff_eq_add] at h
  rw [h, nsmul_eq_mul, add_comm]
  push_cast
  rfl

theorem tendsto_pow (A : Matrix (Fin k) (Fin k) ℤ_[g])
    (hA : UT (A.map (PadicInt.toZMod (p := g)))) :
    Tendsto (fun m => A ^ g ^ m) atTop (𝓝 1) := by
  obtain ⟨Y, hY⟩ := lift_one g k (A ^ g ^ k) (by rw [Matrix.map_pow]; exact red_pow g k hA)
  rw [← tendsto_add_atTop_iff_nat k]
  refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hg1 : (1 : ℝ) < g := by exact_mod_cast (Fact.out : g.Prime).one_lt
  have hlim : Tendsto (fun b : ℕ => ((g : ℝ)⁻¹) ^ (b + 1)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hg1)).comp
      (tendsto_add_atTop_nat 1)
  refine squeeze_zero (fun _ => norm_nonneg _) (fun b => ?_) hlim
  obtain ⟨Z, hZ⟩ := pow_one_add g k Y b
  have e : A ^ g ^ (b + k) = 1 + (g ^ (b + 1)) • Z := by
    rw [pow_add, mul_comm, pow_mul, hY, hZ]
  rw [e, Matrix.add_apply, add_sub_cancel_left, Matrix.smul_apply, nsmul_eq_mul, norm_mul]
  push_cast
  rw [norm_pow, PadicInt.norm_p]
  exact mul_le_of_le_one_right (by positivity) (PadicInt.norm_le_one _)

end UpperTriangularReduction

end Formalism.MainNotions.UnusedSlot33

end
