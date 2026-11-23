import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.ObFacts
import GroundTheory.PAdicHodge.BStPeriod
import GroundTheory.PAdicHodge.KerTheta
import GroundTheory.PAdicHodge.TiltValuation
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.TiltFacts

variable (l : ℕ) [Fact l.Prime]

theorem isDomain_ob : IsDomain (CrystallineSemistableComparison.Ob l) :=
  IsPerfectoidField.isDomain_preTilt (K := ℂ_[l]) l

theorem norm_pFlat_eq : ‖(pFlat l : PreTilt (normInteger ℂ_[l]) l)‖ = ‖(l : ℂ_[l])‖ := by
  rw [preTilt_norm_def, coe_untilt_pFlat]

theorem norm_pFlat_pos : 0 < ‖(pFlat l : PreTilt (normInteger ℂ_[l]) l)‖ := by
  rw [norm_pFlat_eq]
  exact norm_pos_iff.2 (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)

theorem norm_pFlat_lt_one : ‖(pFlat l : PreTilt (normInteger ℂ_[l]) l)‖ < 1 := by
  rw [norm_pFlat_eq]
  exact IsPerfectoidField.norm_natCast_lt_one

theorem rt_pow (k : ℕ) : CrystallineSemistableComparison.D.rt l k ^ l ^ k = pFlat l := by
  have h := (iterateFrobeniusEquiv (CrystallineSemistableComparison.Ob l) l k).apply_symm_apply (pFlat l)
  rwa [iterateFrobeniusEquiv_def] at h

theorem exists_dvd_pFlat_pow (a : CrystallineSemistableComparison.Ob l) (ha : a ≠ 0) : ∃ M : ℕ, a ∣ pFlat l ^ M := by
  obtain ⟨M, hM⟩ := exists_pow_lt_of_lt_one (norm_pos_iff.2 ha) (norm_pFlat_lt_one l)
  refine ⟨M, preTilt_dvd_iff_norm_le.2 ?_⟩
  rw [norm_pow]
  exact hM.le

theorem exists_rt_dvd (a : CrystallineSemistableComparison.Ob l) (ha : ¬ IsUnit a) : ∃ k : ℕ, CrystallineSemistableComparison.D.rt l k ∣ a := by
  have hlt : ‖a‖ < 1 := by
    refine lt_of_le_of_ne (preTilt_norm_le_one a) fun h => ha ?_
    exact (IsPerfectoidField.isUnit_iff_norm_untilt l).2 (by rwa [preTilt_norm_def] at h)
  have hl : 1 < l := (Fact.out : l.Prime).one_lt
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (norm_pFlat_pos l) hlt
  have hnl : n ≤ l ^ n := (Nat.lt_pow_self hl).le
  refine ⟨n, preTilt_dvd_iff_norm_le.2 ?_⟩
  have h1 : ‖a‖ ^ l ^ n ≤ ‖CrystallineSemistableComparison.D.rt l n‖ ^ l ^ n := by
    rw [← norm_pow (CrystallineSemistableComparison.D.rt l n), rt_pow]
    exact (pow_le_pow_of_le_one (norm_nonneg _) hlt.le hnl).trans hn.le
  exact le_of_pow_le_pow_left₀ (pow_ne_zero _ (by omega)) (norm_nonneg _) h1

theorem obFacts : ∀ (l : ℕ) [Fact l.Prime], CrystallineSemistableComparison.D.ObFacts l := by
  intro l _
  haveI := isDomain_ob l
  refine ⟨inferInstance, ?_, exists_dvd_pFlat_pow l, exists_rt_dvd l⟩
  refine (ValuationRing.iff_dvd_total).2 ⟨fun a b => ?_⟩
  rcases le_total ‖a‖ ‖b‖ with h | h
  · exact Or.inr (preTilt_dvd_iff_norm_le.2 h)
  · exact Or.inl (preTilt_dvd_iff_norm_le.2 h)

end GlobalTheory.CompanionTheory.TiltFacts
