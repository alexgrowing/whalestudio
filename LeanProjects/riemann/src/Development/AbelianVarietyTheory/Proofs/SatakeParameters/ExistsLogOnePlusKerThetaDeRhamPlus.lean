import Mathlib
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LMulBeta
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.Pst.LogExist

variable {l : ℕ} [Fact l.Prime]

def logSum (w : Per.AinfP l) (n : ℕ) : Per.AinfP l :=
  ∑ k ∈ Finset.range n, (-1) ^ k * Ring.inverse (((k + 1 : ℕ) : Per.AinfP l)) * w ^ (k + 1)

theorem logSum_succ (w : Per.AinfP l) (n : ℕ) :
    logSum w (n + 1) = logSum w n + (-1) ^ n * Ring.inverse (((n + 1 : ℕ) : Per.AinfP l)) * w ^ (n + 1) := by
  simp only [logSum, Finset.sum_range_succ]

theorem logSum_cauchy {w : Per.AinfP l} (hw : w ∈ Per.kerP l) (n : ℕ) :
    logSum w n ≡ logSum w (n + 1) [SMOD (Per.kerP l ^ n • ⊤ : Submodule (Per.AinfP l) (Per.AinfP l))] := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, logSum_succ, sub_add_cancel_left]
  refine (Ideal.neg_mem_iff _).2 (Ideal.mul_mem_left _ _ ?_)
  exact Ideal.pow_le_pow_right (Nat.le_succ n) (Ideal.pow_mem_pow hw _)

def logP {w : Per.AinfP l} (hw : w ∈ Per.kerP l) : Per.BdRp l :=
  (GlobalTheory.RingIface.exists_bdRp_equiv l).choose.symm (AdicCompletion.mk (Per.kerP l) (Per.AinfP l)
    (AdicCompletion.AdicCauchySequence.mk (Per.kerP l) (Per.AinfP l) (logSum w) (logSum_cauchy hw)))

theorem ev_logP {w : Per.AinfP l} (hw : w ∈ Per.kerP l) (n : ℕ) :
    Per.ev l n (logP hw) = Ideal.Quotient.mk _ (logSum w n) := by
  rw [← (GlobalTheory.RingIface.exists_bdRp_equiv l).choose_spec.2, logP, RingEquiv.apply_symm_apply, AdicCompletion.evalₐ_mk]
  rfl

theorem factorial_mul_logSum (w : Per.AinfP l) (n : ℕ) :
    ((n.factorial : ℕ) : Per.AinfP l) * logSum w n =
      ∑ k ∈ Finset.range n, (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : Per.AinfP l) * w ^ (k + 1) := by
  rw [logSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkn : k + 1 ≤ n := Finset.mem_range.1 hk
  have hd : n.factorial / (k + 1) * (k + 1) = n.factorial :=
    Nat.div_mul_cancel (Nat.dvd_factorial (Nat.succ_pos k) hkn)
  have hu : ((k + 1 : ℕ) : Per.AinfP l) * Ring.inverse (((k + 1 : ℕ) : Per.AinfP l)) = 1 :=
    Ring.mul_inverse_cancel _ (GlobalTheory.RingBasics.isUnit_nat l _ (Nat.succ_ne_zero k))
  have hc : ((n.factorial : ℕ) : Per.AinfP l) = ((n.factorial / (k + 1) : ℕ) : Per.AinfP l) * ((k + 1 : ℕ) : Per.AinfP l) := by
    rw [← Nat.cast_mul, hd]
  rw [hc]
  linear_combination (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : Per.AinfP l) * w ^ (k + 1) * hu

theorem isLogP_logP {w : Per.AinfP l} (hw : w ∈ Per.kerP l) : IsLogP w (logP hw) := by
  intro n
  rw [ev_logP, ← factorial_mul_logSum, map_mul, map_natCast]

theorem exists_isLogP : ∀ (l : ℕ) [Fact l.Prime] (w : Per.AinfP l), w ∈ Per.kerP l → ∃ u : Per.BdRp l, IsLogP w u :=
  fun _ _ _ hw => ⟨logP hw, isLogP_logP hw⟩

end GlobalTheory.Pst.LogExist
