import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsGauss
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsGaussGCTarget
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisGaussNormEventuallyMonomial
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics

noncomputable section

open scoped Formalism.Per
open Filter Topology

namespace GlobalTheory.PMon.Gauss

theorem iSup_monomial_logConvex (c : ℕ → ℝ) (h0 : ∀ n, 0 ≤ c n) (h1 : ∀ n, c n ≤ 1)
    {ρ₁ ρ₂ t : ℝ} (hρ₁ : 0 ≤ ρ₁) (hρ₂ : 0 ≤ ρ₂) (hρ₁1 : ρ₁ ≤ 1) (hρ₂1 : ρ₂ ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (⨆ n, c n * (ρ₁ ^ t * ρ₂ ^ (1 - t)) ^ n) ≤
      (⨆ n, c n * ρ₁ ^ n) ^ t * (⨆ n, c n * ρ₂ ^ n) ^ (1 - t) := by
  have hb : ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ 1 → BddAbove (Set.range fun n => c n * ρ ^ n) := fun ρ h0' h1' =>
    ⟨1, Set.forall_mem_range.2 fun n => mul_le_one₀ (h1 n) (pow_nonneg h0' n) (pow_le_one₀ h0' h1')⟩
  apply ciSup_le
  intro n
  have hc : c n = c n ^ t * c n ^ (1 - t) := by
    rw [← Real.rpow_add' (h0 n) (by norm_num), add_sub_cancel, Real.rpow_one]
  have e : c n * (ρ₁ ^ t * ρ₂ ^ (1 - t)) ^ n = (c n * ρ₁ ^ n) ^ t * (c n * ρ₂ ^ n) ^ (1 - t) := by
    rw [Real.mul_rpow (h0 n) (pow_nonneg hρ₁ n), Real.mul_rpow (h0 n) (pow_nonneg hρ₂ n), mul_pow,
      Real.rpow_pow_comm hρ₁, Real.rpow_pow_comm hρ₂]
    conv_lhs => rw [hc]
    ring
  rw [e]
  have ht1' : 0 ≤ 1 - t := by linarith
  exact mul_le_mul
    (Real.rpow_le_rpow (mul_nonneg (h0 n) (pow_nonneg hρ₁ n)) (le_ciSup (hb ρ₁ hρ₁ hρ₁1) n) ht0)
    (Real.rpow_le_rpow (mul_nonneg (h0 n) (pow_nonneg hρ₂ n)) (le_ciSup (hb ρ₂ hρ₂ hρ₂1) n) ht1')
    (Real.rpow_nonneg (mul_nonneg (h0 n) (pow_nonneg hρ₂ n)) _)
    (Real.rpow_nonneg ((mul_nonneg (h0 n) (pow_nonneg hρ₁ n)).trans (le_ciSup (hb ρ₁ hρ₁ hρ₁1) n)) _)

theorem gA_logConvex (l : ℕ) [Fact l.Prime] (a : Formalism.Per.Ainf l) {ρ₁ ρ₂ t : ℝ} (hρ₁ : 0 ≤ ρ₁) (hρ₂ : 0 ≤ ρ₂)
    (hρ₁1 : ρ₁ ≤ 1) (hρ₂1 : ρ₂ ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    gA l (ρ₁ ^ t * ρ₂ ^ (1 - t)) a ≤ gA l ρ₁ a ^ t * gA l ρ₂ a ^ (1 - t) :=
  iSup_monomial_logConvex _ (fun n => by positivity)
    (fun n => Real.rpow_le_one (norm_nonneg _) ((GlobalTheory.RingBasics.mem_OC _).1 (Subtype.prop _)) (by positivity))
    hρ₁ hρ₂ hρ₁1 hρ₂1 ht0 ht1

theorem rpow_mul_rpow_one_sub_self {a t : ℝ} (ha : 0 ≤ a) : a ^ t * a ^ (1 - t) = a := by
  rw [← Real.rpow_add' ha (by norm_num), add_sub_cancel, Real.rpow_one]

theorem gC_logConvex : ∀ (l : ℕ) [Fact l.Prime] (x : Formalism.Per.Acris l) (ρ₁ ρ₂ t : ℝ), (l : ℝ)⁻¹ ≤ ρ₁ → ρ₁ ≤ ρ₂ →
    ρ₂ < 1 → 0 ≤ t → t ≤ 1 → gC l (ρ₁ ^ t * ρ₂ ^ (1 - t)) x ≤ gC l ρ₁ x ^ t * gC l ρ₂ x ^ (1 - t) := by
  intro l _ x ρ₁ ρ₂ t h1 h12 h2 ht0 ht1
  have hl0 : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  have hρ₁ : 0 < ρ₁ := (inv_pos.2 hl0).trans_le h1
  have hρ₂ : 0 < ρ₂ := hρ₁.trans_le h12
  have ht1' : 0 ≤ 1 - t := by linarith
  set ρ := ρ₁ ^ t * ρ₂ ^ (1 - t) with hρdef
  have hρlo : ρ₁ ≤ ρ := by
    calc ρ₁ = ρ₁ ^ t * ρ₁ ^ (1 - t) := (rpow_mul_rpow_one_sub_self hρ₁.le).symm
      _ ≤ ρ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hρ₁.le h12 ht1') (Real.rpow_nonneg hρ₁.le _)
  have hρhi : ρ ≤ ρ₂ := by
    calc ρ ≤ ρ₂ ^ t * ρ₂ ^ (1 - t) :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hρ₁.le h12 ht0) (Real.rpow_nonneg hρ₂.le _)
      _ = ρ₂ := rpow_mul_rpow_one_sub_self hρ₂.le
  have hρ0 : 0 < ρ := hρ₁.trans_le hρlo
  have G : ∀ σ : ℝ, (l : ℝ)⁻¹ ≤ σ → σ < 1 → IsGauss l σ (gC l σ) := fun σ a b => isGauss_gC_of_le l σ a b
  have Gl : ∀ σ : ℝ, (l : ℝ)⁻¹ ≤ σ → σ < 1 → gC l σ (l : Formalism.Per.Acris l) = σ := by
    intro σ a b
    rw [← map_natCast (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l)) l, (G σ a b).2.2.2.2]
    exact GlobalTheory.GaussSlope.gauss_l l ((inv_pos.2 hl0).le.trans a)
  have g : IsGauss l ρ (gC l ρ) := G ρ (h1.trans hρlo) (hρhi.trans_lt h2)
  have g₁ : IsGauss l ρ₁ (gC l ρ₁) := G ρ₁ h1 (h12.trans_lt h2)
  have g₂ : IsGauss l ρ₂ (gC l ρ₂) := G ρ₂ (h1.trans h12) h2

  have P : ∀ σ : ℝ, (l : ℝ)⁻¹ ≤ σ → σ < 1 → ∀ (k : ℕ) (y : Formalism.Per.Acris l),
      gC l σ ((l : Formalism.Per.Acris l) ^ k * y) = σ ^ k * gC l σ y := by
    intro σ a b k y
    rw [GlobalTheory.GaussSlope.map_pow_mul _ (G σ a b).2.2.2.1, Gl σ a b]

  have hs : ∀ s : Formalism.Per.Acris0 l, gC l ρ (algebraMap (Formalism.Per.Acris0 l) (Formalism.Per.Acris l) s) ≤
      gC l ρ₁ (algebraMap (Formalism.Per.Acris0 l) (Formalism.Per.Acris l) s) ^ t *
        gC l ρ₂ (algebraMap (Formalism.Per.Acris0 l) (Formalism.Per.Acris l) s) ^ (1 - t) := by
    intro s
    obtain ⟨k, a, ha⟩ := GlobalTheory.GaussSlope.exists_pow_mul_eq l s
    set y := algebraMap (Formalism.Per.Acris0 l) (Formalism.Per.Acris l) s
    have e : ∀ σ : ℝ, (l : ℝ)⁻¹ ≤ σ → σ < 1 → σ ^ k * gC l σ y = gA l σ a := by
      intro σ a' b
      rw [← P σ a' b, ha, (G σ a' b).2.2.2.2]
    have key := gA_logConvex l a hρ₁.le hρ₂.le (h12.trans h2.le) h2.le ht0 ht1
    rw [← e ρ (h1.trans hρlo) (hρhi.trans_lt h2), ← e ρ₁ h1 (h12.trans_lt h2), ← e ρ₂ (h1.trans h12) h2,
      Real.mul_rpow (pow_nonneg hρ₁.le _) (g₁.1 y).1, Real.mul_rpow (pow_nonneg hρ₂.le _) (g₂.1 y).1,
      ← Real.rpow_pow_comm hρ₁.le, ← Real.rpow_pow_comm hρ₂.le] at key
    have e2 : (ρ₁ ^ t) ^ k * gC l ρ₁ y ^ t * ((ρ₂ ^ (1 - t)) ^ k * gC l ρ₂ y ^ (1 - t)) =
        ρ ^ k * (gC l ρ₁ y ^ t * gC l ρ₂ y ^ (1 - t)) := by
      rw [hρdef, mul_pow]; ring
    rw [e2] at key
    exact le_of_mul_le_mul_left key (pow_pos hρ0 k)

  have F : ∀ r : ℕ, gC l ρ x ≤ max (max (gC l ρ₁ x) (ρ₁ ^ r) ^ t * max (gC l ρ₂ x) (ρ₂ ^ r) ^ (1 - t)) (ρ ^ r) := by
    intro r
    obtain ⟨s, z, hx⟩ := (GlobalTheory.MemLoc.acris_basic l).2.2.1 x r
    set y := algebraMap (Formalism.Per.Acris0 l) (Formalism.Per.Acris l) s
    have hz : ∀ σ : ℝ, (l : ℝ)⁻¹ ≤ σ → σ < 1 → gC l σ ((l : Formalism.Per.Acris l) ^ r * z) ≤ σ ^ r := by
      intro σ a b
      rw [P σ a b]
      exact mul_le_of_le_one_right (pow_nonneg ((inv_pos.2 hl0).le.trans a) _) ((G σ a b).1 z).2
    have hy : ∀ σ : ℝ, (l : ℝ)⁻¹ ≤ σ → σ < 1 → gC l σ y ≤ max (gC l σ x) (σ ^ r) := by
      intro σ a b
      have : y = x + -((l : Formalism.Per.Acris l) ^ r * z) := by rw [hx]; ring
      rw [this]
      refine ((G σ a b).2.1 _ _).trans (max_le_max le_rfl ?_)
      rw [(G σ a b).2.2.1]
      exact hz σ a b
    conv_lhs => rw [hx]
    refine (g.2.1 _ _).trans (max_le_max ?_ (hz ρ (h1.trans hρlo) (hρhi.trans_lt h2)))
    refine (hs s).trans (mul_le_mul (Real.rpow_le_rpow (g₁.1 y).1 (hy ρ₁ h1 (h12.trans_lt h2)) ht0)
      (Real.rpow_le_rpow (g₂.1 y).1 (hy ρ₂ (h1.trans h12) h2) ht1') (Real.rpow_nonneg (g₂.1 y).1 _)
      (Real.rpow_nonneg ((g₁.1 x).1.trans (le_max_left _ _)) _))
  have T : Tendsto (fun r : ℕ => max (max (gC l ρ₁ x) (ρ₁ ^ r) ^ t * max (gC l ρ₂ x) (ρ₂ ^ r) ^ (1 - t)) (ρ ^ r))
      atTop (𝓝 (max (max (gC l ρ₁ x) 0 ^ t * max (gC l ρ₂ x) 0 ^ (1 - t)) 0)) := by
    have t1 := tendsto_pow_atTop_nhds_zero_of_lt_one hρ₁.le (h12.trans_lt h2)
    have t2 := tendsto_pow_atTop_nhds_zero_of_lt_one hρ₂.le h2
    have t0 := tendsto_pow_atTop_nhds_zero_of_lt_one hρ0.le (hρhi.trans_lt h2)
    exact ((((tendsto_const_nhds.max t1).rpow_const (Or.inr ht0)).mul
      ((tendsto_const_nhds.max t2).rpow_const (Or.inr ht1'))).max t0)
  have := ge_of_tendsto' T F
  rwa [max_eq_left (g₁.1 x).1, max_eq_left (g₂.1 x).1,
    max_eq_left (mul_nonneg (Real.rpow_nonneg (g₁.1 x).1 _) (Real.rpow_nonneg (g₂.1 x).1 _))] at this

end GlobalTheory.PMon.Gauss

end
