import Development.AutomorphicArithmetic.PrimitiveCosets.CoreAtH
import Development.AutomorphicArithmetic.PrimitiveCosets.ToEBij
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameFacts

open UpperTheory.Comparison₂ Deduction.CH Formalism Formalism.HC Formalism.D5 Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LHost NumberField Ideal

theorem UpperTheory.GL.oddQS_le :
    ∀ {φ : Frame} (H : HostRaw φ) (C : ℝ), (φ.o : ℝ) ≤ C → (H.QS : ℝ) ≤ C * φ.ord → ((ordCompl[2] H.QS : ℕ) : ℝ) ≤ C ^ 2 := by
  intro φ H C ho hQ
  have h0 : H.QS ≠ 0 := H.QS_pos.ne'
  have hC : (0 : ℝ) ≤ C := (Nat.cast_nonneg _).trans ho
  have h1 : φ.e + 2 ≤ H.QS.factorization 2 :=
    (Nat.prime_two.pow_dvd_iff_le_factorization h0).1 H.tower_dvd
  have h2 : 2 ^ φ.e * ordCompl[2] H.QS ≤ H.QS := by
    conv_rhs => rw [← Nat.ordProj_mul_ordCompl_eq_self H.QS 2]
    exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right two_pos (by omega))
  have h3 : (φ.ord : ℝ) ≤ φ.o * 2 ^ φ.e := by exact_mod_cast φ.ord_le_o_mul_two_pow
  have h4 : (2 : ℝ) ^ φ.e * ((ordCompl[2] H.QS : ℕ) : ℝ) ≤ H.QS := by exact_mod_cast h2
  have hp : (0 : ℝ) < 2 ^ φ.e := by positivity
  have h5 : (φ.ord : ℝ) ≤ C * 2 ^ φ.e := h3.trans (mul_le_mul_of_nonneg_right ho hp.le)
  refine le_of_mul_le_mul_left ?_ hp
  calc (2 : ℝ) ^ φ.e * ((ordCompl[2] H.QS : ℕ) : ℝ) ≤ C * φ.ord := h4.trans hQ
    _ ≤ C * (C * 2 ^ φ.e) := mul_le_mul_of_nonneg_left h5 hC
    _ = 2 ^ φ.e * C ^ 2 := by ring
