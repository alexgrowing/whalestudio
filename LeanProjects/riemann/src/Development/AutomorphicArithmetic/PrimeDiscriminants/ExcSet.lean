import Mathlib
import Formalism.SharpRestriction.Divisibility.JumpSets
import Formalism.PieriBlockIdeals.PieriColumnMinors.ParameterBounds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumExponentLogLeOfCut

open Formalism.BasicNotions Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds

namespace UpperTheory.ExcSet

theorem mem_ramSet_of_dvd (D : D7) {l : ℕ} (hl : l.Prime) (h : l ∣ D.host.condN) : l ∈ Formalism.MainNotions.JumpSetsAlt.ramSet D := by
  have hq : D.host.q.Prime := D.host.hyp.1
  have hd : D.host.d.Prime := D.host.hyp.2.1
  unfold Formalism.MainNotions.JumpSetsAlt.ramSet Formalism.HC.HostRaw.small
  rcases (Nat.Prime.dvd_mul hl).1 h with h2 | h2
  · rcases (Nat.Prime.dvd_mul hl).1 h2 with h3 | h3
    · exact Finset.mem_union_left _ (Nat.mem_primeFactors.2 ⟨hl, h3, D.host.QS_pos.ne'⟩)
    · simp [(Nat.prime_dvd_prime_iff_eq hl hq).1 h3]
  · simp [(Nat.prime_dvd_prime_iff_eq hl hd).1 h2]

theorem ramSet_subset_excSet (D : D7) : Formalism.MainNotions.JumpSetsAlt.ramSet D ⊆ Formalism.MainNotions.JumpSetsAlt.excSet D := by
  unfold Formalism.MainNotions.JumpSetsAlt.ramSet Formalism.MainNotions.JumpSetsAlt.excSet
  refine Finset.union_subset_union_right fun x hx => ?_
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
  tauto

theorem not_dvd_discr (D : D7) {l : ℕ} (hl : l.Prime) (hS : l ∉ Formalism.MainNotions.JumpSetsAlt.excSet D) :
    ¬ ((l : ℕ) : ℤ) ∣ NumberField.discr D.host.E := fun h =>
  hS (ramSet_subset_excSet D (mem_ramSet_of_dvd D hl (D.host.der.discr_primes.1 l hl h)))

theorem small_le_lJ (D : D7) (P : Par) (hH : P.Hyp) (hL : P.Large) (hf : P.f = D.R.f) (hfk : P.f ≤ P.k)
    {l : ℕ} (hl : l ∈ D.host.small) : (l : ℝ) ≤ P.lJ := by
  have h1 : l ≤ D.host.QS := Nat.le_of_mem_primeFactors hl
  have h2 := D.host.QS_le
  have h3 : D.R.f = 2 * D.R.n := rfl
  have h4 := hH.t_ge
  have h5 := hH.f_pos
  have h6 : l ≤ P.k * P.t := by
    have : D.R.n ^ 2 ≤ P.k * P.t := by
      rw [sq]; exact Nat.mul_le_mul (by omega) (by omega)
    omega
  have h7 : (l : ℝ) ≤ (P.k : ℝ) * (P.t : ℝ) := by exact_mod_cast h6
  have hk : (0 : ℝ) < P.k := by exact_mod_cast (by omega : 0 < P.k)
  have ht : (0 : ℝ) < P.t := by exact_mod_cast (by omega : 0 < P.t)
  have hc := (Formalism.CohomologicalDescent.LogSmallConstantBounds.paramsLJ_holds P hH hL).1
  have hb := hL.b_gt
  refine h7.trans (le_trans ?_ hc)
  rw [le_div_iff₀ (by positivity)]
  nlinarith [mul_pos hk ht, sq_nonneg ((P.k : ℝ) * P.t)]

theorem sum_exponent_log_le (hC : Formalism.CohomologicalDescent.E.ExCut) (D : D7) (P : Par) (X' A : ℝ) (hH : P.Hyp) (hL : P.Large)
    (hR : LargeParameterEstimates.Rows P X' A) (hB : LargeParameterEstimates.Big P.L P.x X' A) (ι : Type) [Fintype ι] [DecidableEq ι] (W : Wts ι) (hW : W.Ok P)
    (hcard : Fintype.card ι = P.f) (hf : P.f = D.R.f) (hSp : W.Sp = Formalism.MainNotions.JumpSetsAlt.excSet D)
    (T : ℕ) (hT : W.T2.card ≤ T) (Q : Finset ℕ) (hQ : ∀ l ∈ Q, l.Prime) :
    ∑ l ∈ Q, (W.Jrec7 P l : ℝ) * Real.log (l : ℝ) ≤
      30 * (T : ℝ) * (P.m : ℝ) * P.b * P.L ^ 2 + 2 * (P.m : ℝ) * P.b := by
  let S : Finset ℕ := {D.host.q, D.host.d, D.host.pde, D.host.pde'}
  let W' : Wts ι := { W with Sp := S }
  have hW' : W'.Ok P := ⟨hW.anti, hW.what₂, hW.block, hW.centre, hW.window, hW.cloud, hW.low, hW.thick, hW.other⟩
  have hS : W'.Sp.card ≤ 5 := (Finset.card_le_four).trans (by norm_num)
  have hJ : ∀ l, W'.Jrec7 P l = W.Jrec7 P l := by
    intro l
    have e : ((l : ℝ) ≤ P.lJ ∨ P.Excl l ∨ l ∈ W'.Sp) ↔ ((l : ℝ) ≤ P.lJ ∨ P.Excl l ∨ l ∈ W.Sp) := by
      rw [hSp]
      show (_ ∨ _ ∨ l ∈ S) ↔ (_ ∨ _ ∨ l ∈ D.host.small ∪ S)
      rw [Finset.mem_union]
      have := fun h => small_le_lJ D P hH hL hf hR.f_le (l := l) h
      tauto
    unfold Wts.Jrec7
    by_cases hc : (l : ℝ) ≤ P.lJ ∨ P.Excl l ∨ l ∈ W.Sp
    · rw [if_pos hc, if_pos (e.2 hc)]; rfl
    · rw [if_neg hc, if_neg (fun h => hc (e.1 h))]; rfl
  have h := GlobalTheory.sum_exponent_log_le_of_cut hC P X' A hH hL hR hB ι W' hW' hcard hS T hT Q hQ
  simpa only [hJ] using h

end UpperTheory.ExcSet
