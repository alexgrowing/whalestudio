import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsScaledPeriodPairInvariantsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegersLatticeInvariantsNeZeroStatement

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

theorem exists_ker_point_sqrtNegNat {p : ℕ} (hp : 1 < p) (L : PeriodPair)
    (hL : MulStable L (sqrtNegNat p)) :
    ∃ t : ℂ, t ∉ L.lattice ∧ sqrtNegNat p * t ∈ L.lattice := by
  have hn : Complex.normSq (sqrtNegNat p) = p := by
    rw [sqrtNegNat, map_mul, Complex.normSq_I, Complex.normSq_ofReal,
      Real.mul_self_sqrt (Nat.cast_nonneg p), mul_one]
  have hp' : (1 : ℝ) < p := by exact_mod_cast hp
  have h0 : sqrtNegNat p ≠ 0 := fun h => by
    rw [h, map_zero] at hn
    linarith
  obtain ⟨S, hS⟩ := kerRepsExist L _ h0 hL
  have hc := kerRepsCard L _ S h0 hL hS
  rw [hn] at hc
  have hpos : S.Nonempty := by
    rw [← Finset.card_pos]
    have : (0 : ℝ) < S.card := by
      push_cast at hc
      linarith
    exact_mod_cast this
  obtain ⟨t, ht⟩ := hpos
  have := hS.1 t ht
  exact ⟨t, by tauto, by tauto⟩

theorem g₂_mem_adjoin_j_of_eq (L : PeriodPair) (h0 : L.g₂ ≠ 0) (h : L.g₃ = L.g₂) :
    L.g₂ ∈ ℚ⟮(latticeCurve L).j⟯ := by
  have hΔ := latticeCurve_Δ_ne_zero L
  rw [latticeCurve_Δ, h] at hΔ
  have h27 : L.g₂ - 27 ≠ 0 := fun e => hΔ (by linear_combination L.g₂ ^ 2 * e)
  have hj : (latticeCurve L).j = 1728 * L.g₂ / (L.g₂ - 27) := by
    rw [latticeCurve_j_eq, h, div_eq_div_iff hΔ h27]
    ring
  have hj' : (latticeCurve L).j - 1728 = 1728 * 27 / (L.g₂ - 27) := by
    rw [hj]
    field_simp
    ring
  have e : L.g₂ = 27 * (latticeCurve L).j / ((latticeCurve L).j - 1728) := by
    rw [hj', hj]
    field_simp
  have hm := IntermediateField.mem_adjoin_simple_self ℚ (latticeCurve L).j
  rw [e]
  exact div_mem (mul_mem (ofNat_mem _ 27) hm) (sub_mem hm (ofNat_mem _ 1728))

theorem exists_datum_of_isIntegersLattice : ∀ (p : ℕ) (L₀ : PeriodPair), p.Prime → p % 4 = 3 →
    3 < p → IsIntegersLattice p L₀ → ∃ (L : PeriodPair) (t : ℂ),
      Datum p ℚ⟮(latticeCurve L₀).j⟯ L t ∧ (latticeCurve L).j = (latticeCurve L₀).j := by
  intro p L₀ hp _ h3 hL₀
  obtain ⟨h2, h3', hmul⟩ := GlobalTheory.T.integersLattice_g2_g3_ne_zero_and_mulStable p L₀ hp h3 hL₀
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (L₀.g₃ / L₀.g₂) two_pos
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact div_ne_zero h3' h2 (by rw [← hc]; simp)
  obtain ⟨L, hlat, hg2, hg3, -, hj⟩ := GlobalTheory.T.exists_scaled_periodPair_invariants L₀ c hc0
  have hmul' : MulStable L (sqrtNegNat p) := by
    intro ω hω
    have h1 : c⁻¹ * ω ∈ L₀.lattice := (hlat _).mp (by rwa [mul_inv_cancel_left₀ hc0])
    have h2 := (hlat _).mpr (hmul _ h1)
    rwa [mul_left_comm, mul_inv_cancel_left₀ hc0] at h2
  have hne : L.g₂ ≠ 0 := by
    rw [hg2]
    exact mul_ne_zero (inv_ne_zero (pow_ne_zero _ hc0)) h2
  have heq : L.g₃ = L.g₂ := by
    have : L₀.g₃ = c ^ 2 * L₀.g₂ := by rw [hc, div_mul_cancel₀ _ h2]
    rw [hg2, hg3, this]
    field_simp
  have hmem := g₂_mem_adjoin_j_of_eq L hne heq
  rw [hj] at hmem
  obtain ⟨t, ht, ht'⟩ := exists_ker_point_sqrtNegNat hp.one_lt L hmul'
  exact ⟨L, t, ⟨hmul', hmem, heq ▸ hmem, ht, ht'⟩, hj⟩

end GlobalTheory.CMModel
