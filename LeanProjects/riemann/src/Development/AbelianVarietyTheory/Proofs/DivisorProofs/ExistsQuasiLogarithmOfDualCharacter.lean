import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FormalExpMulFormalExpNeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCharSeriesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubstGroupLawEqMulOfDualTateCharacterStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerSeriesLinearCoefficientsMvPowerSeriesFormalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Cob1FormalLogMapMemKerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusFormalLogSubSmulIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DlogEqSumLinearCoefficientsFormExplicitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodFormalLogLiftCharacterSeriesStatement

namespace GlobalTheory.CharLog

variable {p : ℕ} {B O Q : Type} [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] {θ : B →+* O}

theorem isUnit_intCast [Fact p.Prime] (h : GlobalTheory.QLog.IsFrame p Q θ) {n : ℤ} (hn : n ≠ 0) :
    IsUnit (n : Q) := by
  have hna : n.natAbs ≠ 0 := Int.natAbs_ne_zero.2 hn
  obtain ⟨k, m, hm, hnm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hna p (Fact.out : p.Prime).ne_one
  have hcop : Nat.Coprime m p :=
    Nat.coprime_comm.1 (((Fact.out : p.Prime).coprime_iff_not_dvd).2 hm)
  have hu : IsUnit (n.natAbs : Q) := by
    rw [hnm, Nat.cast_mul, Nat.cast_pow]
    refine (h.unit_p.pow k).mul ?_
    simpa using (h.unit_coprime m hcop).map (algebraMap B Q)
  rcases Int.natAbs_eq n with h' | h'
  · rw [h', Int.cast_natCast]; exact hu
  · rw [h', Int.cast_neg, Int.cast_natCast]; exact hu.neg

noncomputable def ratAlgebra [Fact p.Prime] (h : GlobalTheory.QLog.IsFrame p Q θ) : Algebra ℚ Q :=
  (IsLocalization.lift (M := nonZeroDivisors ℤ) (S := ℚ) (g := Int.castRingHom Q)
    fun y => by simpa using isUnit_intCast h (nonZeroDivisors.ne_zero y.2)).toAlgebra

end GlobalTheory.CharLog

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc

theorem GlobalTheory.CharLog.exists_log_char_period : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = c.μ i) → ∀ χ : G.dual.Tate, ∃ (f : MvPowerSeries (Fin d) F.Q) (w : Fin d → F.B), QL μ' ⊤ f ∧ In (RingHom.ker F.θ) (cob1 (up F.Q μ') f) ∧ In (⊤ : Ideal F.B) (frob p F.s f - (p : F.Q) • f) ∧ (∀ i, lin f i = algebraMap F.B F.Q (w i)) ∧ dlog G χ = ∑ i, F.θ (w i) • c.form i ∧ ∀ t, c.HasPeriod F.θ t f (F.a (Sandwich.mu ε * ofPadic p O (epsPairing hε G t χ))) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε F G d c μ' hlift hμ χ
  letI : Algebra ℚ F.Q := GlobalTheory.CharLog.ratAlgebra F.frame
  obtain ⟨u, hu0, hu⟩ := GlobalTheory.T.exists_charSeries' p O G d c χ
  have hmul := GlobalTheory.T.subst_groupLaw_eq_mul_of_dualTateCharacter p O G d c χ u hu
  choose g0 hg0 using fun α => F.frame.surj (coeff α u)
  let g : MvPowerSeries (Fin d) F.B := fun α => if α = 0 then 1 else g0 α
  have hg : map F.θ g = u := by
    ext α
    rw [coeff_map]
    by_cases h : α = 0
    · subst h
      change F.θ (if (0 : Fin d →₀ ℕ) = 0 then 1 else g0 0) = _
      rw [if_pos rfl, map_one, coeff_zero_eq_constantCoeff_apply, hu0]
    · change F.θ (if α = 0 then 1 else g0 α) = _
      rw [if_neg h, hg0]
  have hg1 : constantCoeff g = 1 := by
    rw [← coeff_zero_eq_constantCoeff_apply]
    change (if (0 : Fin d →₀ ℕ) = 0 then 1 else g0 0) = 1
    rw [if_pos rfl]
  have hlin : ∀ i, lin (formalLog (map (algebraMap F.B F.Q) g)) i =
      algebraMap F.B F.Q (coeff (Finsupp.single i 1) g) := fun i => by
    rw [GlobalTheory.T.powerSeriesLinearCoefficients_mvPowerSeriesFormalLog F.Q d _ (by rw [constantCoeff_map, hg1, map_one]) i, lin, coeff_map]
  have hcob := GlobalTheory.T.cob1_formalLog_mem_ker_of_map_grouplike p F.B O F.Q F.θ F.frame d μ' hlift.const g hg1 (by
    rw [hg]; convert hmul using 2; funext i; exact hμ i)
  refine ⟨formalLog (map (algebraMap F.B F.Q) g), fun i => coeff (Finsupp.single i 1) g,
    ⟨constantCoeff_formalLog (by rw [constantCoeff_map, hg1, map_one]),
      fun i => ⟨_, Submodule.mem_top, hlin i⟩,
      fun α => by obtain ⟨b, -, hb⟩ := hcob α; exact ⟨b, Submodule.mem_top, hb⟩⟩,
    hcob, GlobalTheory.T.frobenius_formalLog_sub_smul_integral p F.B O F.Q F.θ F.frame F.σ F.s F.s_alg F.σ_pow d g hg1, hlin, ?_, ?_⟩
  · rw [GlobalTheory.T.dlog_eq_sum_linearCoefficients_form_explicit p O G d c χ u hu0 hu]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hg, lin, coeff_map]
  · exact GlobalTheory.T.period_formalLog_lift_characterSeries p C v O hv ε hε F G d c χ g hg1 (by rw [hg]; exact hu)
