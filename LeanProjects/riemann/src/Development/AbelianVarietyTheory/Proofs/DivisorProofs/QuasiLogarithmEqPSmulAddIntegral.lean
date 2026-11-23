import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KatzQuasiIntegralCriterionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvPowerSeriesReductionModPrimeRulesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReductionCommutesFormalGroupLawCoboundariesStatement
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Katz

theorem exists_p_mul_of_constantCoeff_eq_zero (p : ℕ) [Fact p.Prime] {k : Type} [Field k]
    [CharP k p] [PerfectRing k p] (a : WittVector p k) (ha : WittVector.constantCoeff a = 0) :
    ∃ c : WittVector p k, a = (p : WittVector p k) * c := by
  by_cases h0 : a = 0
  · exact ⟨0, by simp [h0]⟩
  obtain ⟨m, b, hb, rfl⟩ := WittVector.exists_eq_pow_p_mul a h0
  cases m with
  | zero =>
    exfalso; apply hb
    simpa using ha
  | succ m => exact ⟨(p : WittVector p k) ^ m * b, by ring⟩

theorem formalGroupLawCoboundaryOne_sub_eq {R : Type} [CommRing R] {d : ℕ} {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R}
    (h : ∀ i, constantCoeff (μ i) = 0) (f g : MvPowerSeries (Fin d) R) :
    cob1 μ (f - g) = cob1 μ f - cob1 μ g := by
  have := formalCoboundary_add h (f - g) g
  rw [sub_add_cancel] at this
  rw [this]; abel

theorem quasiLog_eq_p_smul_add_int : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    [PerfectRing k p] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) (h : IsLaw μ),
    ∀ f ∈ quasiLog p h, ∀ b, Red p (cob1 (fun i => Katz.lift p (μ i)) f) (cob1 μ b) →
      RedV p (lin f) (lin b) →
      ∃ g ∈ quasiLog p h, f - (p : WittVector p k) • g ∈ intBy p k (Fin d) 1 := by
  intro p _ k _ _ _ d μ h f hf b hcf hlf
  obtain ⟨R1, -, R3, R4, -, R6, ZariskiNoetherianInduction⟩ := GlobalTheory.T.mvPowerSeries_reduction_mod_prime_rules p k (Fin d)
  obtain ⟨-, R1', -, -⟩ := GlobalTheory.T.mvPowerSeries_reduction_mod_prime_rules p k (Fin d ⊕ Fin d)
  have hL : ∀ i, constantCoeff (Katz.lift p (μ i)) = 0 := fun i => constantCoeff_lift p (h.const i)
  obtain ⟨-, C2, -, -⟩ := GlobalTheory.T.reduction_commutes_formalGroupLawCoboundaries p k d μ h.const
  obtain ⟨hcb, hlb⟩ := C2 (Katz.lift p b) b (R3 b)
  set f' := f - Katz.lift p b with hf'

  have hc' : cob1 (fun i => Katz.lift p (μ i)) f' ∈ intBy p k (Fin d ⊕ Fin d) (p : WittVector p k) := by
    obtain ⟨-, -, -, S4, -, S6, -⟩ := GlobalTheory.T.mvPowerSeries_reduction_mod_prime_rules p k (Fin d ⊕ Fin d)
    rw [S6, hf', formalGroupLawCoboundaryOne_sub_eq hL]
    have := (S4 _ _ _ _ hcf hcb).2
    rwa [sub_self] at this
  obtain ⟨-, -, -, -, -, -, S7⟩ := GlobalTheory.T.mvPowerSeries_reduction_mod_prime_rules p k (Fin d ⊕ Fin d)
  obtain ⟨c0, hc0, hc0e⟩ := (S7 _ _).1 hc'
  have hpW : (p : WittVector p k) ≠ 0 := WittVector.p_nonzero p k
  have hpF : (p : Fr p k) ≠ 0 := by
    have : (p : Fr p k) = algebraMap (WittVector p k) (Fr p k) (p : WittVector p k) := by simp
    rw [this]
    exact fun h0 => hpW (IsFractionRing.injective (WittVector p k) (Fr p k) (by simpa using h0))
  have hsm : ∀ {σ : Type} (x : MvPowerSeries σ (Fr p k)),
      (p : WittVector p k) • x = (p : Fr p k) • x := by
    intro σ x
    rw [← algebraMap_smul (Fr p k) (p : WittVector p k) x]
    simp
  have hcg : cob1 (fun i => Katz.lift p (μ i)) ((p : Fr p k)⁻¹ • f') ∈ intBy p k _ 1 := by
    rw [formalCoboundary_smul hL, hc0e, hsm, smul_smul, inv_mul_cancel₀ hpF, one_smul]
    exact hc0
  refine ⟨(p : Fr p k)⁻¹ • f', ⟨?_, hcg⟩, ?_⟩
  · apply GlobalTheory.T.katz_quasi_integral_criterion p k d μ h _ _ hcg
    intro i
    obtain ⟨a, ha, ha0⟩ := hlf i
    obtain ⟨a', ha', ha0'⟩ := hlb i
    obtain ⟨c, hc⟩ := exists_p_mul_of_constantCoeff_eq_zero p (a - a') (by
      rw [map_sub, ha0, ha0', sub_self])
    refine ⟨c, ?_⟩
    have e1 : lin f' i = algebraMap (WittVector p k) (Fr p k) (a - a') := by
      simp only [lin, hf', map_sub] at ha ha' ⊢
      rw [ha, ha']
    have e2 : lin ((p : Fr p k)⁻¹ • f') i = (p : Fr p k)⁻¹ * lin f' i := by
      simp [lin]
    rw [e2, e1, hc, map_mul]
    simp [hpF]
  · rw [hsm, smul_smul, mul_inv_cancel₀ hpF, one_smul, hf', sub_sub_cancel]
    exact (R1 _).2 ⟨b, R3 b⟩

end GlobalTheory.Katz
