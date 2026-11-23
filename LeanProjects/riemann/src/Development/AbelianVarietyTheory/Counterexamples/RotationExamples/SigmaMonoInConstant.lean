import Mathlib
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.FunctionalLowerBoundOfConditionsNumeric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FpTiedIffExistsLeafFP

open Module NumberField IsDedekindDomain
open scoped Matrix nonZeroDivisors

noncomputable section

namespace GlobalTheory.FinitePlacesProbe

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.Indef.Tree

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {Df : DefSide Bs}

def LocalAt (O : FunData K Df) (t : Bs.Tup) (w : HeightOneSpectrum (𝓞 K)) (δ : ℤ) : Prop :=
  Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (matLat (O.vmu t) (Df.Mt t)) ≤
    Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (Formalism.HermitianLatticesTheory.idealSmul
      (((w.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ (-δ) : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) O.M)

theorem logArg_nonneg (O : FunData K Df) {b : ℝ} (hb : 1 ≤ b) :
    0 ≤ Real.log (b * O.nr * O.g1 * O.g2 * O.pd * O.pd' * |(O.dE : ℝ)|) := by
  have e : b * O.nr * O.g1 * O.g2 * O.pd * O.pd' * |(O.dE : ℝ)| =
      b * ((O.nr * O.g1 * O.g2 * O.pd * O.pd' * O.dE.natAbs : ℕ) : ℝ) := by
    push_cast [Nat.cast_natAbs]; ring
  rw [e]
  rcases Nat.eq_zero_or_pos (O.nr * O.g1 * O.g2 * O.pd * O.pd' * O.dE.natAbs) with h | h
  · rw [h]; simp
  · exact Real.log_nonneg (one_le_mul_of_one_le_of_one_le hb (by exact_mod_cast h))

theorem sigma_mono_in_constant (O : FunData K Df) {C C' b : ℝ} (h : C ≤ C') (hb : 1 ≤ b) : O.Sig0 C b ≤ O.Sig0 C' b := by
  refine Finset.sum_le_sum fun q _ => mul_le_mul_of_nonneg_right ?_ (Real.log_natCast_nonneg _)
  have : O.ee C b q ≤ O.ee C' b q := by
    unfold FunData.ee
    split_ifs
    · refine Nat.succ_le_succ (Nat.floor_le_floor (div_le_div_of_nonneg_right ?_ (Real.log_natCast_nonneg _)))
      unfold FunData.PPF
      have := logArg_nonneg O hb
      gcongr
    · exact le_rfl
  exact_mod_cast this

theorem monotonicity₂ (O : FunData K Df) {C C' b : ℝ} (h0 : 0 ≤ C) (h : C ≤ C') (hb : 1 ≤ b) : O.bFP C b ≤ O.bFP C' b := by
  have h1 := sigma_mono_in_constant O h hb
  have h2 := Sig0_nonneg O C b
  have h3 := Real.log_nonneg hb
  have h4 : 0 ≤ C' := h0.trans h
  have h5 : 0 ≤ b := by linarith
  unfold FunData.bFP
  gcongr

end GlobalTheory.FinitePlacesProbe
