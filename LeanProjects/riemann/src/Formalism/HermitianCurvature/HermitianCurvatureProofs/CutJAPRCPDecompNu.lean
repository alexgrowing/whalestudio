import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRCPDecompPS

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP.Dc

open Formalism.FourierDecayAlt.P.B2x3 Formalism.FourierDecayAlt.P.SettingConstruction Formalism.FourierDecayAlt.P.TheSec Formalism.FourierDecayAlt.B2

noncomputable section

set_option linter.unusedSimpArgs false

variable {k : ℕ}

def Su (k : ℕ) (i j : Fin (k + 1)) : Mb k := Matrix.single i j 1

lemma Su_mul (i j j' m : Fin (k + 1)) : Su k i j * Su k j' m = if j = j' then Su k i m else 0 := by
  unfold Su
  split_ifs with h
  · subst h
    rw [Matrix.single_mul_single_same, mul_one]
  · rw [Matrix.single_mul_single_of_ne _ _ _ _ h]

def nuG (k : ℕ) (v s w : ℂ) : Mb k :=
  1 + (v - 1) • Su k 0 0 + s • (Su k 0 (Fin.last k) + Su k (Fin.last k) 0) + (w - 1) • Su k (Fin.last k) (Fin.last k)

lemma nu_eq (w s : ℂ) : nu k w s = nuG k (star w) s w := by
  unfold nu nuG Su
  simp only [Matrix.single_eq_single_vecMulVec_single, Matrix.add_vecMulVec, Matrix.smul_vecMulVec]
  module

lemma dnu_eq (a b c : ℂ) : dnu k a b c =
    a • Su k 0 0 + b • (Su k 0 (Fin.last k) + Su k (Fin.last k) 0) + c • Su k (Fin.last k) (Fin.last k) := rfl

lemma nuG_mul (h0 : (0 : Fin (k + 1)) ≠ Fin.last k) (v s w : ℂ) (hw : w * v - s * s = 1) :
    nuG k v s w * nuG k w (-s) v = 1 := by
  simp only [nuG, mul_add, add_mul, Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one, Su_mul, h0, h0.symm, if_true,
    if_false, smul_zero, add_zero, zero_add]
  linear_combination (norm := module) hw • (Su k 0 0 + Su k (Fin.last k) (Fin.last k))

lemma conj_corner_matrix_unit (h0 : (0 : Fin (k + 1)) ≠ Fin.last k) (v s w : ℂ) :
    nuG k w (-s) v * Su k 0 0 * nuG k v s w = (w * v) • Su k 0 0 + (w * s) • Su k 0 (Fin.last k) -
      (s * v) • Su k (Fin.last k) 0 - (s * s) • Su k (Fin.last k) (Fin.last k) := by
  simp only [nuG, mul_add, add_mul, Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one, Su_mul, h0, h0.symm, if_true,
    if_false, smul_zero, add_zero, zero_add]
  module

lemma conj0m (h0 : (0 : Fin (k + 1)) ≠ Fin.last k) (v s w : ℂ) (m : Fin (k + 1)) (hm0 : m ≠ 0) (hml : m ≠ Fin.last k) :
    nuG k w (-s) v * Su k 0 m * nuG k v s w = w • Su k 0 m - s • Su k (Fin.last k) m := by
  simp only [nuG, mul_add, add_mul, Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one, Su_mul, h0, h0.symm, hm0, hml,
    hm0.symm, hml.symm, if_true, if_false, smul_zero, add_zero, zero_add]
  module

lemma conjm0 (h0 : (0 : Fin (k + 1)) ≠ Fin.last k) (v s w : ℂ) (m : Fin (k + 1)) (hm0 : m ≠ 0) (hml : m ≠ Fin.last k) :
    nuG k w (-s) v * Su k m 0 * nuG k v s w = v • Su k m 0 + s • Su k m (Fin.last k) := by
  simp only [nuG, mul_add, add_mul, Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one, Su_mul, h0, h0.symm, hm0, hml,
    hm0.symm, hml.symm, if_true, if_false, smul_zero, add_zero, zero_add]
  module

lemma nuI_dnu (h0 : (0 : Fin (k + 1)) ≠ Fin.last k) (v s w a b c : ℂ) :
    nuG k w (-s) v * dnu k a b c = (w * a - s * b) • Su k 0 0 + (w * b - s * c) • Su k 0 (Fin.last k) +
      (-s * a + v * b) • Su k (Fin.last k) 0 + (-s * b + v * c) • Su k (Fin.last k) (Fin.last k) := by
  simp only [nuG, dnu_eq, mul_add, add_mul, Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one, Su_mul, h0, h0.symm, if_true,
    if_false, smul_zero, add_zero, zero_add]
  module

lemma unit0l (h0 : (0 : Fin (k + 1)) ≠ Fin.last k) (v s w c p : ℂ) (hs : s ≠ 0) (hc : c ≠ 0) (hv : v ≠ 0)
    (hw : w * v - s * s = 1) (hp : 2 * s * p = -c * v) :
    Su k 0 (Fin.last k) = (-(v / (2 * s))) • Su k 0 0 + nuG k w (-s) v * ((v / (2 * s)) • Su k 0 0) * nuG k v s w +
      (-(s / c)) • (nuG k w (-s) v * dnu k 0 p (-c)) := by
  have hw' : w = (1 + s * s) / v := by field_simp; linear_combination hw
  have hp' : p = -c * v / (2 * s) := by field_simp; linear_combination hp
  subst hw' hp'
  rw [Matrix.mul_smul, Matrix.smul_mul, conj_corner_matrix_unit h0, nuI_dnu h0]
  match_scalars <;> field_simp <;> ring

lemma unitl0 (h0 : (0 : Fin (k + 1)) ≠ Fin.last k) (v s w c q : ℂ) (hs : s ≠ 0) (hc : c ≠ 0) (hv : v ≠ 0)
    (hw : w * v - s * s = 1) (hq : 2 * s * q = -c * w) :
    Su k (Fin.last k) 0 = (w / (2 * s)) • Su k 0 0 + nuG k w (-s) v * ((-(w / (2 * s))) • Su k 0 0) * nuG k v s w +
      (-(s / c)) • (nuG k w (-s) v * dnu k (-c) q 0) := by
  have hw' : w = (1 + s * s) / v := by field_simp; linear_combination hw
  subst hw'
  have hq' : q = -c * ((1 + s * s) / v) / (2 * s) := by field_simp; field_simp at hq; linear_combination hq
  subst hq'
  rw [Matrix.mul_smul, Matrix.smul_mul, conj_corner_matrix_unit h0, nuI_dnu h0]
  match_scalars <;> field_simp <;> ring

lemma unitll (h0 : (0 : Fin (k + 1)) ≠ Fin.last k) (v s w c p q : ℂ) (hs : s ≠ 0) (hc : c ≠ 0) (hv : v ≠ 0)
    (hw : w * v - s * s = 1) (hp : 2 * s * p = -c * v) (hq : 2 * s * q = -c * w) :
    Su k (Fin.last k) (Fin.last k) = nuG k w (-s) v * Su k 0 0 * nuG k v s w +
      (-(w / c)) • (nuG k w (-s) v * dnu k 0 p (-c)) + (v / c) • (nuG k w (-s) v * dnu k (-c) q 0) := by
  have hw' : w = (1 + s * s) / v := by field_simp; linear_combination hw
  subst hw'
  have hp' : p = -c * v / (2 * s) := by field_simp; linear_combination hp
  have hq' : q = -c * ((1 + s * s) / v) / (2 * s) := by field_simp; field_simp at hq; linear_combination hq
  subst hp' hq'
  rw [conj_corner_matrix_unit h0, nuI_dnu h0, nuI_dnu h0]
  match_scalars <;> field_simp <;> ring

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP.Dc
