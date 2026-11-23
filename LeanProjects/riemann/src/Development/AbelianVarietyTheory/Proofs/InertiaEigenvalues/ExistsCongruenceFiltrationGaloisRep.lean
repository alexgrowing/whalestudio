import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CongruenceSubgroupsGLPadicStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowPrimeSubOneNormLeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MatrixNearOnePowPrimeDeepStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon
open scoped Formalism.Per

namespace GlobalTheory

theorem congrFilt_le_all_eq_zero (l : ℕ) [hl : Fact l.Prime] (x : ℝ) (hx0 : 0 ≤ x)
    (h : ∀ k : ℕ, x ≤ (l : ℝ) ^ (-((k : ℤ) + 2))) : x = 0 := by
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.out.one_lt
  by_contra hne
  have hpos : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hne)
  have hinv : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl1
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hpos hinv
  have h1 : (l : ℝ) ^ (-((k : ℤ) + 2)) ≤ (l : ℝ) ^ (-(k : ℤ)) :=
    zpow_le_zpow_right₀ hl1.le (by omega)
  have h2 : (l : ℝ) ^ (-(k : ℤ)) = ((l : ℝ)⁻¹) ^ k := by
    rw [zpow_neg, zpow_natCast, inv_pow]
  linarith [h k]

theorem congrFiltration : ∀ (l : ℕ) [Fact l.Prime] (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (ρ : ↥(GK K) →* GL n ℚ_[l]), (∀ i j, Continuous fun g => (ρ g : Matrix n n ℚ_[l]) i j) → ∃ N : ℕ → Subgroup ↥(GK K), (∀ k g, g ∈ N k ↔ ∀ i j, ‖((ρ g : Matrix n n ℚ_[l]) - 1) i j‖ ≤ (l : ℝ) ^ (-((k : ℤ) + 2))) ∧ Antitone N ∧ (∀ k, IsOpen (N k : Set ↥(GK K))) ∧ (∀ k g, g ∈ N k → g ^ l ∈ N (k + 1)) ∧ (∀ k g, g ∈ N 0 → g ^ l ∈ N (k + 1) → g ∈ N k) ∧ ∀ g, (∀ k, g ∈ N k) → ρ g = 1 := by
  intro l _ n _ _ K ρ hcont
  obtain ⟨Γ, hΓ⟩ := GlobalTheory.T.exists_congruenceSubgroups_GL_padic l n
  have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast (Fact.out : l.Prime).one_lt.le
  have hmem : ∀ k g, g ∈ (Γ k).comap ρ ↔ ∀ i j, ‖((ρ g : Matrix n n ℚ_[l]) - 1) i j‖ ≤ (l : ℝ) ^ (-((k : ℤ) + 2)) := by
    intro k g
    rw [Subgroup.mem_comap, hΓ]
  refine ⟨fun k => (Γ k).comap ρ, hmem, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b hab g hg
    rw [hmem] at hg ⊢
    intro i j
    have hab' : (a : ℤ) ≤ b := by exact_mod_cast hab
    exact le_trans (hg i j) (zpow_le_zpow_right₀ hl1 (by omega))
  · intro k
    have hset : (((Γ k).comap ρ : Subgroup ↥(GK K)) : Set ↥(GK K)) =
        ⋂ i, ⋂ j, (fun g => ((ρ g : Matrix n n ℚ_[l]) - 1) i j) ⁻¹'
          Metric.closedBall (0 : ℚ_[l]) ((l : ℝ) ^ (-((k : ℤ) + 2))) := by
      ext g
      simp only [SetLike.mem_coe, hmem, Set.mem_iInter, Set.mem_preimage, mem_closedBall_zero_iff]
    rw [hset]
    refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
    have hc : Continuous fun g => ((ρ g : Matrix n n ℚ_[l]) - 1) i j := by
      simp only [Matrix.sub_apply]
      exact (hcont i j).sub continuous_const
    exact (IsUltrametricDist.isOpen_closedBall (0 : ℚ_[l])
      (zpow_pos (by linarith) _).ne').preimage hc
  · intro k g hg
    rw [hmem] at hg ⊢
    have := GlobalTheory.T.norm_pow_prime_sub_one_le_of_norm_sub_one_le l n (ρ g : Matrix n n ℚ_[l]) k hg
    simpa [map_pow, Units.val_pow_eq_pow_val] using this
  · intro k g h0 hk
    rw [hmem] at h0 hk ⊢
    have h0' : ∀ i j, ‖((ρ g : Matrix n n ℚ_[l]) - 1) i j‖ ≤ (l : ℝ) ^ (-2 : ℤ) := by
      simpa using h0
    have hk' : ∀ i j, ‖((ρ g : Matrix n n ℚ_[l]) ^ l - 1) i j‖ ≤ (l : ℝ) ^ (-(((k + 1 : ℕ) : ℤ) + 2)) := by
      simpa [map_pow, Units.val_pow_eq_pow_val] using hk
    exact GlobalTheory.T.norm_sub_one_le_of_norm_pow_prime_sub_one_le l n _ k h0' hk'
  · intro g hg
    apply Units.ext
    ext i j
    have hz : ‖((ρ g : Matrix n n ℚ_[l]) - 1) i j‖ = 0 :=
      congrFilt_le_all_eq_zero l _ (norm_nonneg _) fun k => (hmem k g).1 (hg k) i j
    rw [norm_eq_zero, Matrix.sub_apply, sub_eq_zero] at hz
    simpa using hz

end GlobalTheory
