import Formalism.ThetaLogCoordinates.BihomogeneousPairs.LetterChainEmbeddings.PairStep
import Formalism.MahlerMeasure.MahlerMeasureProofs.PhiInt

namespace Formalism.InvariantFactorPaths.KP.LL

open Formalism.GM

open MvPolynomial Finset Formalism.GM.M

theorem tieP_smul {k σ : Type} [Field k] {r : ℕ} (w e : Fin r → σ) (zv sv : σ) (o n z : ℕ) (c : k)
    (y : MvPolynomial σ k) : tieP w e zv sv o n z (c • y) = c • tieP w e zv sv o n z y := by
  unfold tieP
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [mul_smul_comm, map_smul, map_smul, smul_comm]

theorem pst_scal_mem {p : ℕ} [Fact p.Prime] {σ : Type} (Λ : Submodule ℤ_[p] (MvPolynomial σ ℚ_[p]))
    (a u m j k : ℕ) (hk : k ≤ j) (hu : a + Nat.log p j ≤ u) (s : ℚ_[p]) (hs : ‖s‖ ≤ 1)
    (y : MvPolynomial σ ℚ_[p])
    (hy : (((p : ℚ_[p]) ^ a * ((m.factorial : ℚ_[p]) ^ 2)⁻¹) • y) ∈ Λ) :
    ((s * (p : ℚ_[p]) ^ u * (((m.factorial : ℚ_[p]) ^ 2) * ((j.choose k : ℕ) : ℚ_[p]))⁻¹) • y) ∈ Λ := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hu
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le one_pos hp1
  have e1 : (s * (p : ℚ_[p]) ^ (a + Nat.log p j + d) *
      (((m.factorial : ℚ_[p]) ^ 2) * ((j.choose k : ℕ) : ℚ_[p]))⁻¹) • y =
      (s * (p : ℚ_[p]) ^ d * ((p : ℚ_[p]) ^ (Nat.log p j) * (((j.choose k : ℕ) : ℚ_[p]))⁻¹)) •
        (((p : ℚ_[p]) ^ a * ((m.factorial : ℚ_[p]) ^ 2)⁻¹) • y) := by
    rw [smul_smul, mul_inv, pow_add, pow_add]
    congr 1
    ring
  rw [e1]
  refine smul_mem_of_norm Λ ?_ hy
  have hpn : ∀ t : ℕ, ‖(p : ℚ_[p]) ^ t‖ = ((p : ℝ) ^ t)⁻¹ := by
    intro t
    rw [norm_pow, Padic.norm_p, inv_pow]
  rw [norm_mul, norm_mul, norm_mul, hpn, hpn]
  have h1 : ((p : ℝ) ^ d)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hp1)
  have h2 : ((p : ℝ) ^ (Nat.log p j))⁻¹ * ‖(((j.choose k : ℕ) : ℚ_[p]))⁻¹‖ ≤ 1 := by
    have := PhiIntegrality.norm_choose_inv_le (p := p) j k hk
    rw [inv_mul_le_iff₀ (pow_pos hp0 _), mul_one]
    exact this
  have h3 : ‖s‖ * ((p : ℝ) ^ d)⁻¹ ≤ 1 :=
    mul_le_one₀ hs (inv_nonneg.mpr (pow_pos hp0 _).le) h1
  exact mul_le_one₀ h3 (mul_nonneg (inv_nonneg.mpr (pow_pos hp0 _).le) (norm_nonneg _)) h2

theorem pair_induction_holds : PairStep := by
  intro p _ σ r w e zv sv hr hz o n z L u Λ h1 h2 hu l hl x hx
  constructor
  · rw [decomp w e zv sv hr hz (o - l) (n - l) z x (h1 l x hx), Finset.mul_sum, Finset.smul_sum]
    refine Submodule.sum_mem _ (fun m hm => ?_)
    simp only [mem_range] at hm
    refine Submodule.subset_span ⟨l + m, by omega,
      ((1 : ℚ_[p]) * (p : ℚ_[p]) ^ u * (((m.factorial : ℚ_[p]) ^ 2) *
        (((o - l + (n - l) + r + z - m).choose m : ℕ) : ℚ_[p]))⁻¹) • (tieF w e ^ m) x, ?_, ?_⟩
    · refine pst_scal_mem (Λ (l + m)) (r * L) u m _ m (by omega) ?_ 1 (by simp) _ (h2 l m (by omega) x hx)
      exact le_trans (Nat.add_le_add_left (Nat.log_mono_right (by omega)) _) hu
    · rw [Nat.sub_sub, Nat.sub_sub, one_mul, mul_smul, tieP_smul w e zv sv _ _ _ ((p : ℚ_[p]) ^ u),
        mul_smul_comm, pow_add, mul_assoc]
  · rw [harmonicProjection_expand w e zv sv hz, Finset.mul_sum, Finset.smul_sum]
    refine Submodule.sum_mem _ (fun m hm => ?_)
    by_cases hmm : min (o - l) (n - l) < m
    · rw [h1 l x hx m hmm]
      simp
    · refine Submodule.subset_span ⟨l + m, by omega,
        ((-1 : ℚ_[p]) ^ m * (p : ℚ_[p]) ^ u * (((m.factorial : ℚ_[p]) ^ 2) *
          (((o - l + (n - l) + r + z - 1).choose m : ℕ) : ℚ_[p]))⁻¹) • (tieF w e ^ m) x, ?_, ?_⟩
      · refine pst_scal_mem (Λ (l + m)) (r * L) u m _ m (by omega) ?_ _ (by simp) _ (h2 l m (by omega) x hx)
        exact le_trans (Nat.add_le_add_left (Nat.log_mono_right (by omega)) _) hu
      · simp only [smul_eq_C_mul, div_eq_mul_inv, map_mul]
        ring

end Formalism.InvariantFactorPaths.KP.LL
