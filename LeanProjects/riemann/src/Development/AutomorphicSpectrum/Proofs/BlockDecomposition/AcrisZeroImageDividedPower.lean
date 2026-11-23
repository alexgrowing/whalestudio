import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.EtaleComparisonMapOfFacts
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry Opposite GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.CompanionTheory.LogEpsP

variable {l : ℕ} [Fact l.Prime]

theorem cris_eq_zero (A : PAlg l) (n : ℕ) {y : Acris l}
    (hy : y ∈ Ideal.span {(l : Acris l)} ^ n) : A.cris n y = 0 := by
  rw [Ideal.span_singleton_pow] at hy
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hy
  rw [map_mul, map_pow, map_natCast, PAlg.pow_l_acr, mul_zero]

theorem cris_log (A : PAlg l) (n : ℕ) {x : Ainf l} (hx : x ∈ RingHom.ker (theta0 l)) :
    A.cris n (ACris.log hx) = ∑ k ∈ Finset.range (l * n), A.cris n (ACris.logTerm hx k) := by
  obtain ⟨N, hN⟩ := ACris.isAdicSum_log hx n
  have h2 := cris_eq_zero A n (hN (max N (l * n)) (le_max_left _ _))
  rw [map_sub, sub_eq_zero, map_sum,
    ← Finset.sum_range_add_sum_Ico _ (le_max_right N (l * n)),
    Finset.sum_eq_zero (s := Finset.Ico (l * n) (max N (l * n))) (fun k hk =>
      cris_eq_zero A n (ACris.logTerm_mem hx (Finset.mem_Ico.1 hk).1)), add_zero] at h2
  exact h2

theorem cris_logTerm (A : PAlg l) (n k : ℕ) {x : Ainf l} (hx : x ∈ RingHom.ker (theta0 l)) :
    A.cris n (ACris.logTerm hx k) =
      (-1) ^ k * (k.factorial : A.Acr n) * A.mkAcr n (A.cris0 (ACris.dpowZero hx (k + 1))) := by
  rw [ACris.logTerm, AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    PAlg.cris_of, ACris.logTermZero]
  simp only [map_mul, map_pow, map_neg, map_one, map_natCast]

theorem acrisZero_image_divided_power (A : PAlg l) (k : ℕ) {x : Ainf l} (hx : x ∈ RingHom.ker (theta0 l)) :
    (A.cris0 (ACris.dpowZero hx k)).1 = dpw k (WittVector.map A.s x) :=
  awayW_dpw A.s k (ACris.isUnit_natCast (K := ℂ_[l]) (p := l) k.factorial_ne_zero) x

theorem map_mu (A : PAlg l) (e : Ob l) :
    WittVector.map A.s (AInf.mu (K := ℂ_[l]) (p := l) e) = WittVector.teichmuller l (A.s e) - 1 := by
  rw [AInf.mu, map_sub, map_one, WittVector.map_teichmuller]

end GlobalTheory.CompanionTheory.LogEpsP

theorem GlobalTheory.CompanionTheory.LogEpsP.logEps : CrystallineSemistableComparison.E.LogEps := by
  intro l _ A n
  refine ⟨fun k => A.cris0 (ACris.dpowZero (ACris.mu_mem_ker (untilt_epsilon (p := l))) k), fun k => ?_, ?_⟩
  · rw [GlobalTheory.CompanionTheory.LogEpsP.acrisZero_image_divided_power, GlobalTheory.CompanionTheory.LogEpsP.map_mu]
  · rw [ACris.periodT, GlobalTheory.CompanionTheory.LogEpsP.cris_log]
    exact Finset.sum_congr rfl fun k _ => GlobalTheory.CompanionTheory.LogEpsP.cris_logTerm A n k _
