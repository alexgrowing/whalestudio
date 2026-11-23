import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankCyclotomicExtAndCyclotomicCharSurjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharacterPadicBasicProperties
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicNormZpowSubOnePadicValInt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormUnitPowSubOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCyclotomicFrobeniusTwistedValueEqPowMulStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualExpTeichmullerPowerSumFormulaStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicTowerFrobeniusFormulaPosWeightStatement
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

noncomputable section

namespace GlobalTheory.ExpImage

variable {l : ℕ} [Fact l.Prime]

theorem norm_algebraMap_mul (κ : ℚ_[l]) (α : Om l) :
    ‖algebraMap ℚ_[l] (Om l) κ * α‖ = ‖κ‖ * ‖α‖ := by
  rw [norm_mul, PadicAlgCl.norm_extends]

theorem exists_gen (P : LocPrime l) (K : FinExt l) {s : ℕ} (hs : Lev l s) :
    ∃ g ∈ Gj K s, (P.χQ g : ℚ_[l]) = ((1 + l ^ s : ℕ) : ℚ_[l]) := by
  have hn : ‖((1 + l ^ s : ℕ) : ℚ_[l]) - 1‖ = (l : ℝ) ^ (-(s : ℤ)) := by
    push_cast
    rw [add_sub_cancel_left, Padic.norm_p_pow]
  have hu : ‖((1 + l ^ s : ℕ) : ℚ_[l])‖ = 1 := by
    rw [Padic.norm_natCast_eq_one_iff]
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le' hs.1
    rw [hk, pow_succ]
    simp
  obtain ⟨g, hg, hχ⟩ := (GlobalTheory.Cyc.finrank_Ks_and_chi_surjective l K).2 P.χQ P.χQ_cyc _ hu
  exact ⟨g, (((GlobalTheory.Cyc.cyc_basic l P.χQ P.χQ_cyc).2.2 K g hg).1 s).2 (by rw [hχ, hn]), hχ⟩

theorem expStar_image : ∀ (D : Formalism.BasicNotions.D7) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ), Lev l s → ∀ e : ℕ, ∀ α : Om l, α ∈ Ks K s → ‖α‖ ≤ 1 → ∃ z : GQ l → ℚ_[l], (∀ σ ∈ Gj K s, ‖z σ‖ ≤ 1) ∧ ExpStar D.loc (Gj K s) e z ((l : Om l) ^ (betaE l s e) * α) := by
  intro D l _ K s hs e α hα hα1
  obtain ⟨g, hg, hχ⟩ := exists_gen (D.loc l) K hs
  set u : ℚ_[l] := ((1 + l ^ s : ℕ) : ℚ_[l]) with hu
  have hl0 : (l : ℚ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hlr : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  have hn : ‖u - 1‖ = (l : ℝ) ^ (-(s : ℤ)) := by
    rw [hu]
    push_cast
    rw [add_sub_cancel_left, Padic.norm_p_pow]
  have hlog : ‖logZl l u‖ = (l : ℝ) ^ (-(s : ℤ)) := by
    rw [(GlobalTheory.PadicLogUnits.logZl_hom l).2.2.2 s hs.1 hs.2 u hn.le, hn]
  have key : ∀ ρ : ℚ_[l], ‖ρ‖ = (l : ℝ) ^ (((e + 1) * (s - 1) : ℕ) - betaE l s e) →
      (∀ (lam : ℕ → ↥(K0 K)) (d : ↥(K0 K)), (∀ a, ‖(lam a : Om l)‖ ≤ 1) → ‖(d : Om l)‖ ≤ 1 →
        d - (l : ↥(K0 K)) ^ e * frK (D.loc l) K d = (frK (D.loc l) K ^ s) (∑ a ∈ primeTo l s, lam a) →
        ∃ z : GQ l → ℚ_[l], (∀ σ ∈ Gj K s, ‖z σ‖ ≤ 1) ∧ ExpStar D.loc (Gj K s) e z
          (algebraMap ℚ_[l] (Om l) ρ * cycVal (D.loc l) K s e lam d)) →
      ∃ z : GQ l → ℚ_[l], (∀ σ ∈ Gj K s, ‖z σ‖ ≤ 1) ∧
        ExpStar D.loc (Gj K s) e z ((l : Om l) ^ (betaE l s e) * α) := by
    intro ρ hρ H
    have hρ0 : ρ ≠ 0 := by
      rw [← norm_ne_zero_iff, hρ]
      exact (zpow_pos hlr _).ne'
    set κ : ℚ_[l] := (l : ℚ_[l]) ^ (betaE l s e) / (ρ * (l : ℚ_[l]) ^ ((e + 1) * (s - 1))) with hκ
    have hκ1 : ‖κ‖ = 1 := by
      rw [hκ, norm_div, norm_mul, hρ, Padic.norm_p_zpow, Padic.norm_p_pow, ← zpow_add₀ hlr.ne',
        div_eq_one_iff_eq (zpow_pos hlr _).ne']
      congr 1
      ring
    obtain ⟨lam, d, h1, h2, h3, h4⟩ := GlobalTheory.T.exists_cyclotomicFrobeniusTwistedValue_eq_pow_mul l (D.loc l) K s e hs.1 (algebraMap ℚ_[l] (Om l) κ * α)
      (mul_mem (IntermediateField.algebraMap_mem _ _) hα) (by rw [norm_algebraMap_mul, hκ1, one_mul]; exact hα1)
    obtain ⟨z, hz, hE⟩ := H lam d h1 h2 h3
    refine ⟨z, hz, ?_⟩
    convert hE using 1
    have : ρ * (l : ℚ_[l]) ^ ((e + 1) * (s - 1)) * κ = (l : ℚ_[l]) ^ (betaE l s e) := by
      rw [hκ]
      field_simp
    have h5 := congrArg (algebraMap ℚ_[l] (Om l)) this
    rw [map_mul, map_mul, map_pow, map_zpow₀, map_natCast] at h5
    rw [h4, ← h5]
    ring
  obtain ⟨s', rfl⟩ := Nat.exists_eq_add_of_le' hs.1
  rcases Nat.eq_zero_or_pos e with rfl | he
  · refine key (logZl l u * (((0 : ℕ).factorial : ℚ_[l]) * (l : ℚ_[l]) ^ ((s' + 1) * 0)))⁻¹ ?_ ?_
    · simp only [Nat.factorial_zero, Nat.cast_one, mul_zero, pow_zero, mul_one, norm_inv, hlog, betaE]
      rw [← zpow_neg]
      congr 1
      simp
    · intro lam d h1 h2 h3
      have := GlobalTheory.T.dualExp_teichmuller_power_sum_formula D.loc l (D.locA l) (D.locT l) K (s' + 1) hs 0 g hg hχ ℕ (primeTo l (s' + 1)) lam id
        (fun _ => d) (fun i hi => ⟨h1 i, (Finset.mem_filter.1 hi).2⟩)
        (fun j hj => by
          obtain rfl : j = 0 := Nat.le_zero.1 hj
          exact ⟨h2, by simpa using h3⟩)
      convert this using 5
      simp [cycVal, levSum]
  · refine key _ ?_ (GlobalTheory.T.cyclotomicTower_frobenius_formula_pos_weight D.loc l (D.locA l) (D.locT l) K (s' + 1) hs e he g hg hχ)
    obtain ⟨e', rfl⟩ := Nat.exists_eq_add_of_le' he
    have h6 := GlobalTheory.Cyc.LiftExp.norm_zpow_sub_one l (s' + 1) hs u hn ((e' + 1 : ℕ) : ℤ) (by omega)
    rw [zpow_natCast, padicValInt.of_nat] at h6
    have h7 : ‖(((e' + 1).factorial : ℕ) : ℚ_[l])‖ =
        (l : ℝ) ^ (-((padicValNat l (e' + 1) : ℤ) + (padicValNat l e'.factorial : ℤ))) := by
      rw [Padic.norm_eq_zpow_neg_valuation (by exact_mod_cast (e' + 1).factorial_ne_zero),
        Padic.valuation_natCast, Nat.factorial_succ,
        padicValNat.mul (Nat.succ_ne_zero _) e'.factorial_ne_zero]
      push_cast
      rfl
    rw [← hu, norm_div, norm_mul, norm_mul, h6, hlog, h7, Padic.norm_p_pow, ← zpow_add₀ hlr.ne',
      ← zpow_add₀ hlr.ne', ← zpow_sub₀ hlr.ne']
    congr 1
    simp only [betaE, Nat.add_sub_cancel, Nat.succ_ne_zero, if_false]
    push_cast
    ring

end GlobalTheory.ExpImage
