import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.SstPer

variable {l : ℕ} [Fact l.Prime]

variable (l) in

def ecoefQ (k₀ k i : ℕ) : ℚ_[l] := (l : ℚ_[l]) ^ k₀ * ((i.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (k * i))⁻¹

variable (l) in

def ecoef (k₀ k i : ℕ) : ℤ_[l] :=
  ⟨if ‖ecoefQ l k₀ k i‖ ≤ 1 then ecoefQ l k₀ k i else 0, by
    split_ifs with h
    · exact h
    · simp⟩

def kap (C : Core l) {K : FinExt l} (bk : BK K) {d : ℕ} (k₀ k : ℕ) (Mn : Matrix (Fin d) (Fin d) (Wq l bk.a))
    (z : ℤ_[l]) : Matrix (Fin d) (Fin d) (Per.Acris l) :=
  ∑ i ∈ Finset.range d, (algebraMap (Ainf l) (Per.Acris l) (Per.zA l (ecoef l k₀ k i)) *
    (algebraMap (Ainf l) (Per.Acris l) (Per.zA l z) * C.t) ^ i) •
      (Mn.map (((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev).comp PowerSeries.C)) ^ i

theorem ecoefQ_norm_le {d e m : ℕ} (k : ℕ) (hm : ¬ l ∣ m) (hd : d.factorial = l ^ e * m) {i : ℕ} (hi : i < d) :
    ‖ecoefQ l (e + k * d) k i‖ ≤ 1 := by
  obtain ⟨q, hq⟩ := Nat.factorial_dvd_factorial hi.le
  obtain ⟨r, rfl⟩ : ∃ r, d = i + r := ⟨d - i, by omega⟩
  have hl0 : (l : ℚ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hm0 : (m : ℚ_[l]) ≠ 0 := by
    rintro h
    exact hm (by rw [Nat.cast_eq_zero.1 h]; exact dvd_zero _)
  have hf0 : (i.factorial : ℚ_[l]) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero i)
  have h : (l : ℚ_[l]) ^ e * m = i.factorial * q := by
    exact_mod_cast (hd.symm.trans hq)
  have e1 : ecoefQ l (e + k * (i + r)) k i = (l : ℚ_[l]) ^ (k * r) * q * (m : ℚ_[l])⁻¹ := by
    unfold ecoefQ
    rw [show e + k * (i + r) = e + k * i + k * r by ring]
    field_simp
    rw [pow_add, pow_add]
    linear_combination ((l : ℚ_[l]) ^ (k * i) * (l : ℚ_[l]) ^ (k * r)) * h
  rw [e1, norm_mul, norm_mul, norm_inv, (Padic.norm_natCast_eq_one_iff (p := l)).2 ((Nat.Prime.coprime_iff_not_dvd (Fact.out : l.Prime)).2 hm), inv_one, mul_one]
  have h1 : ‖(l : ℚ_[l]) ^ (k * r)‖ ≤ 1 := by
    rw [norm_pow, Padic.norm_p]
    exact pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt.le))
  have h2 : ‖(q : ℚ_[l])‖ ≤ 1 := by exact_mod_cast Padic.norm_int_le_one (q : ℤ)
  calc ‖(l : ℚ_[l]) ^ (k * r)‖ * ‖(q : ℚ_[l])‖ ≤ 1 * 1 := mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

theorem ecoef_val {k₀ k i : ℕ} (h : ‖ecoefQ l k₀ k i‖ ≤ 1) :
    ((ecoef l k₀ k i : ℤ_[l]) : ℚ_[l]) = ecoefQ l k₀ k i := by
  show (if ‖ecoefQ l k₀ k i‖ ≤ 1 then ecoefQ l k₀ k i else 0) = _
  rw [if_pos h]

theorem kap_zero (C : Core l) {K : FinExt l} (bk : BK K) {d : ℕ} (k₀ k : ℕ) (Mn : Matrix (Fin d) (Fin d) (Wq l bk.a)) :
    kap C bk k₀ k Mn 0 = (l : Per.Acris l) ^ k₀ • (1 : Matrix (Fin d) (Fin d) (Per.Acris l)) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · exact Subsingleton.elim _ _
  unfold kap
  rw [Finset.sum_eq_single 0]
  · have h0 : ecoef l k₀ k 0 = (l : ℤ_[l]) ^ k₀ := by
      have hn : ‖ecoefQ l k₀ k 0‖ ≤ 1 := by
        simp only [ecoefQ, Nat.factorial_zero, Nat.cast_one, mul_zero, pow_zero, mul_one, inv_one]
        rw [norm_pow, Padic.norm_p]
        exact pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt.le))
      apply Subtype.ext
      rw [ecoef_val hn]
      simp [ecoefQ]
    simp [h0]
  · intro i _ hi
    simp [zero_pow hi]
  · intro h
    exact absurd (Finset.mem_range.2 hd) h

end GlobalTheory.SstPer

end
