import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicLevelIntegersMemClosureLevelsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCyclotomicFrobeniusTwistedValueEqStatement

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

namespace GlobalTheory.ExpImage

theorem cycVal_add {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (s e : ℕ)
    (lam lam' : ℕ → ↥(K0 K)) (d d' : ↥(K0 K)) :
    cycVal P K s e (fun a => lam a + lam' a) (d + d') =
      cycVal P K s e lam d + cycVal P K s e lam' d' := by
  unfold cycVal
  simp only [map_add]
  push_cast
  simp only [add_mul, Finset.sum_add_distrib, mul_add]
  ring

theorem cycVal_neg {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (s e : ℕ)
    (lam : ℕ → ↥(K0 K)) (d : ↥(K0 K)) :
    cycVal P K s e (fun a => -lam a) (-d) = -cycVal P K s e lam d := by
  unfold cycVal
  simp only [map_neg]
  push_cast
  simp only [neg_mul, Finset.sum_neg_distrib, mul_neg]
  ring

theorem cycVal_zero {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (s e : ℕ) :
    cycVal P K s e (fun _ => 0) 0 = 0 := by
  simp [cycVal]

theorem exists_cycVal_eq_pow_mul (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (s e : ℕ)
    (hs : 1 ≤ s) (α : Om l) (hα : α ∈ Ks K s) (hn : ‖α‖ ≤ 1) :
    ∃ (lam : ℕ → ↥(K0 K)) (d : ↥(K0 K)), (∀ a, ‖(lam a : Om l)‖ ≤ 1) ∧ ‖(d : Om l)‖ ≤ 1 ∧
      d - (l : ↥(K0 K)) ^ e * frK P K d = (frK P K ^ s) (∑ a ∈ primeTo l s, lam a) ∧
      cycVal P K s e lam d = (l : Om l) ^ ((e + 1) * (s - 1)) * α := by
  have hl1 : 1 < l := (Fact.out : l.Prime).one_lt
  have hsum := GlobalTheory.ExpImage.Values.sum_zeta P
  have hgeom : ∑ r ∈ Finset.range l, P.ζQ 1 ^ r = 0 := by
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega), hsum]
    simp
  have hpow : P.ζQ 1 ^ l = 1 := by
    have h := geom_sum_mul (P.ζQ 1) l
    rw [hgeom, zero_mul] at h
    exact (sub_eq_zero.mp h.symm)
  have h0 : P.ζQ 0 = 1 := by
    have h := GlobalTheory.ExpImage.Values.zeta_pow P 0 1
    simpa [hpow] using h.symm
  have h1 : P.ζQ 1 ≠ 1 := by
    intro h
    rw [h] at hsum
    have hc : ((l - 1 : ℕ) : Om l) = -1 := by simpa using hsum
    have hz : ((l : ℕ) : Om l) = 0 := by
      push_cast [Nat.cast_sub hl1.le] at hc
      linear_combination hc
    exact (Nat.cast_ne_zero.mpr (by omega : l ≠ 0)) hz
  have hchain : ∀ j, P.ζQ (j + 1) ^ l = P.ζQ j := fun j => by
    simpa using GlobalTheory.ExpImage.Values.zeta_pow P j 1
  have hmem := GlobalTheory.T.cyclotomicLevel_integers_mem_closure_levels l K P.ζQ h0 h1 hchain s hs α hα hn
  clear hα hn
  induction hmem using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨j, n, c, hj, hjs, hn', hc, hc1, rfl⟩ := hx
    exact GlobalTheory.T.exists_cyclotomicFrobeniusTwistedValue_eq l P K s e j n hj hjs hn' c hc hc1
  | zero =>
    refine ⟨fun _ => 0, 0, fun _ => by simp, by simp, by simp, ?_⟩
    rw [cycVal_zero, mul_zero]
  | add x y _ _ ihx ihy =>
    obtain ⟨lam, d, hlam, hd, hfr, hv⟩ := ihx
    obtain ⟨lam', d', hlam', hd', hfr', hv'⟩ := ihy
    refine ⟨fun a => lam a + lam' a, d + d', fun a => ?_, ?_, ?_, ?_⟩
    · push_cast
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hlam a) (hlam' a))
    · push_cast
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hd hd')
    · simp only [map_add, Finset.sum_add_distrib]
      rw [← hfr, ← hfr']
      ring
    · rw [cycVal_add, hv, hv']
      ring
  | neg x _ ih =>
    obtain ⟨lam, d, hlam, hd, hfr, hv⟩ := ih
    refine ⟨fun a => -lam a, -d, fun a => by simpa using hlam a, by simpa using hd, ?_, ?_⟩
    · simp only [map_neg, Finset.sum_neg_distrib]
      rw [← hfr]
      ring
    · rw [cycVal_neg, hv]
      ring

end GlobalTheory.ExpImage
