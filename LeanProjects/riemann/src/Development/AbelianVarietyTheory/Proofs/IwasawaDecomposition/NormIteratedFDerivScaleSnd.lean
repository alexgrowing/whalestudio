import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemSupportBDIff
import ReciprocityTheory.L2DbarEstimates.Localization.ChartA

open Filter Topology Set Function
open scoped ContDiff

namespace GlobalTheory.BorelParam

variable {E F G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem ray_iteratedDeriv (f : E → G) (hf : ContDiff ℝ ∞ f) (a v : E) (n : ℕ) :
    iteratedDeriv n (fun t : ℝ => f (a + t • v)) 0 = iteratedFDeriv ℝ n f a (fun _ => v) := by
  have e : (fun t : ℝ => f (a + t • v)) =
      (fun y => f (a + y)) ∘ (ContinuousLinearMap.toSpanSingleton ℝ v) := by
    funext t; simp
  have hf' : ContDiff ℝ ∞ (fun y => f (a + y)) := hf.comp (contDiff_const.add contDiff_id)
  rw [iteratedDeriv_eq_iteratedFDeriv, e, ContinuousLinearMap.iteratedFDeriv_comp_right _
    hf' _ (by exact_mod_cast le_top)]
  simp [iteratedFDeriv_comp_add_left]

theorem iteratedDeriv_pow_smul_zero (m n : ℕ) (c : G) :
    iteratedDeriv n (fun t : ℝ => t ^ m • c) 0 = if n = m then (m.factorial : ℝ) • c else 0 := by
  rw [iteratedDeriv_smul_const (by fun_prop) c, iteratedDeriv_fun_pow_zero]
  split_ifs <;> simp

theorem contDiff_smul_of_tsupport (W : Set E) (φ : E → ℝ) (g : E → G) (hW : IsOpen W)
    (hg : ContDiffOn ℝ ∞ g W) (hφ : ContDiff ℝ ∞ φ) (hφW : tsupport φ ⊆ W) :
    ContDiff ℝ ∞ (fun x => φ x • g x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ W
  · exact hφ.contDiffAt.smul (hg.contDiffAt (hW.mem_nhds hx))
  · have hx' : x ∉ tsupport φ := fun h => hx (hφW h)
    have h0 : (fun x => φ x • g x) =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [(isClosed_tsupport φ).isOpen_compl.mem_nhds hx'] with y hy
      simp [image_eq_zero_of_notMem_tsupport hy]
    exact contDiffAt_const.congr_of_eventuallyEq h0

theorem norm_iteratedFDeriv_scale_snd (g : E × F → G) (hg : ContDiff ℝ ∞ g) (k : ℕ) (M l : ℝ)
    (hl : 1 ≤ l) (hM : ∀ x, ‖iteratedFDeriv ℝ k g x‖ ≤ M) (x : E × F) :
    ‖iteratedFDeriv ℝ k (fun y : E × F => g (y.1, l • y.2)) x‖ ≤ M * l ^ k := by
  let L : E × F →L[ℝ] E × F :=
    (ContinuousLinearMap.fst ℝ E F).prod (l • ContinuousLinearMap.snd ℝ E F)
  have e : (fun y : E × F => g (y.1, l • y.2)) = g ∘ L := by
    funext y; simp [L]
  rw [e, L.iteratedFDeriv_comp_right hg x (by exact_mod_cast le_top)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hL : ‖L‖ ≤ l := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by linarith) fun y => ?_
    have h1 : ‖L y‖ = max ‖y.1‖ (l * ‖y.2‖) := by
      simp [L, Prod.norm_def, norm_smul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ l)]
    rw [h1, Prod.norm_def]
    refine max_le ?_ ?_
    · calc ‖y.1‖ ≤ l * ‖y.1‖ := le_mul_of_one_le_left (norm_nonneg _) hl
        _ ≤ l * max ‖y.1‖ ‖y.2‖ := mul_le_mul_of_nonneg_left (le_max_left _ _) (by linarith)
    · exact mul_le_mul_of_nonneg_left (le_max_right _ _) (by linarith)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact mul_le_mul (hM _) (pow_le_pow_left₀ (norm_nonneg _) hL k) (by positivity)
    ((norm_nonneg _).trans (hM x))

theorem series_smooth [CompleteSpace G] (h : ℕ → E → G) (hh : ∀ i, ContDiff ℝ ∞ (h i)) (B : ℕ → ℕ → ℝ)
    (hB : ∀ k i x, ‖iteratedFDeriv ℝ k (h i) x‖ ≤ B k i)
    (hB2 : ∀ k i, k < i → B k i ≤ (1 / 2 : ℝ) ^ i) :
    ContDiff ℝ ∞ (fun x => ∑' i, h i x) ∧ ∀ (k : ℕ) x w,
      iteratedFDeriv ℝ k (fun x => ∑' i, h i x) x w = ∑' i, iteratedFDeriv ℝ k (h i) x w := by
  have hv : ∀ k, Summable (B k) := by
    intro k
    rw [← summable_nat_add_iff (k + 1)]
    refine Summable.of_nonneg_of_le (fun i => (norm_nonneg _).trans (hB k _ 0))
      (fun i => hB2 k (i + (k + 1)) (by omega)) ?_
    exact (summable_nat_add_iff (k + 1)).mpr summable_geometric_two
  refine ⟨contDiff_tsum (N := ⊤) hh (fun k _ => hv k) (fun k i x _ => hB k i x), fun k x w => ?_⟩
  have hs : Summable (fun i => iteratedFDeriv ℝ k (h i) x) :=
    Summable.of_norm_bounded (hv k) (fun i => hB k i x)
  rw [iteratedFDeriv_tsum_apply (N := ⊤) hh (fun k _ => hv k) (fun k i x _ => hB k i x)
    (by exact_mod_cast le_top)]
  exact ContinuousMultilinearMap.tsum_eval hs w

end GlobalTheory.BorelParam

namespace GlobalTheory.BorelParam

theorem borel_param : ∀ (d : ℕ) (U C : Set (ReciprocityTheory.L2DbarEstimates.V d)), IsOpen U → IsCompact C → C ⊆ U →
    ∀ p : ℕ → ReciprocityTheory.L2DbarEstimates.V d × ReciprocityTheory.L2DbarEstimates.V d → ReciprocityTheory.L2DbarEstimates.V d,
    (∀ n, ContDiffOn ℝ ∞ (p n) (U ×ˢ Set.univ)) →
    (∀ n, ∀ z ∈ U, ∀ (t : ℝ) ξ, p n (z, t • ξ) = t ^ n • p n (z, ξ)) →
    ∃ f : ReciprocityTheory.L2DbarEstimates.V d × ReciprocityTheory.L2DbarEstimates.V d → ReciprocityTheory.L2DbarEstimates.V d, ContDiff ℝ ∞ f ∧
      ∀ z ∈ C, ∀ ξ n, iteratedDeriv n (fun t : ℝ => f (z, t • ξ)) 0 = p n (z, ξ) := by
  intro d U C hU hC hCU p hp hhom
  obtain ⟨ρ, hρd, hρc, hρU, O, -, hCO, hρ1⟩ := ReciprocityTheory.L2DbarEstimates.F.chT_plateau C U hC hU hCU
  let χ : ContDiffBump (0 : ReciprocityTheory.L2DbarEstimates.V d) := ⟨1, 2, one_pos, one_lt_two⟩
  let g : ℕ → ReciprocityTheory.L2DbarEstimates.V d × ReciprocityTheory.L2DbarEstimates.V d → ReciprocityTheory.L2DbarEstimates.V d :=
    fun m x => (ρ x.1 * χ x.2 / (m.factorial : ℝ)) • p m x
  have hgd : ∀ m, ContDiff ℝ ∞ (g m) := by
    intro m
    refine contDiff_smul_of_tsupport (U ×ˢ Set.univ) _ (p m) (hU.prod isOpen_univ) (hp m)
      (((hρd.comp contDiff_fst).mul (χ.contDiff.comp contDiff_snd)).div_const _) ?_
    refine (closure_minimal ?_ ((isClosed_tsupport ρ).preimage continuous_fst)).trans ?_
    · intro x hx
      refine subset_tsupport ρ ?_
      intro h0
      exact hx (by simp [h0])
    · intro x hx
      exact ⟨hρU hx, Set.mem_univ _⟩
  have hgc : ∀ m, HasCompactSupport (g m) := by
    intro m
    refine HasCompactSupport.intro (hρc.prod χ.hasCompactSupport) ?_
    intro x hx
    simp only [Set.mem_prod, not_and_or] at hx
    rcases hx with hx | hx
    · simp [g, image_eq_zero_of_notMem_tsupport hx]
    · simp [g, image_eq_zero_of_notMem_tsupport hx]
  have hMex : ∀ m k, ∃ M, ∀ x, ‖iteratedFDeriv ℝ k (g m) x‖ ≤ M := fun m k =>
    ((hgd m).continuous_iteratedFDeriv (by exact_mod_cast le_top)).bounded_above_of_compact_support
      ((hgc m).iteratedFDeriv k)
  choose M hM using hMex
  let Mp : ℕ → ℕ → ℝ := fun m k => max (M m k) 0
  let lam : ℕ → ℝ := fun m => 1 + 2 ^ m * ∑ k ∈ Finset.range m, Mp m k
  have hMp0 : ∀ m k, 0 ≤ Mp m k := fun m k => le_max_right _ _
  have hlam1 : ∀ m, 1 ≤ lam m := fun m => by
    have : 0 ≤ 2 ^ m * ∑ k ∈ Finset.range m, Mp m k :=
      mul_nonneg (by positivity) (Finset.sum_nonneg fun k _ => hMp0 m k)
    simp only [lam]; linarith
  have hlam0 : ∀ m, 0 < lam m := fun m => lt_of_lt_of_le one_pos (hlam1 m)
  let term : ℕ → ReciprocityTheory.L2DbarEstimates.V d × ReciprocityTheory.L2DbarEstimates.V d → ReciprocityTheory.L2DbarEstimates.V d :=
    fun m x => ((lam m)⁻¹ ^ m) • g m (x.1, lam m • x.2)
  have htd : ∀ m, ContDiff ℝ ∞ (term m) := fun m =>
    ((hgd m).comp (contDiff_fst.prodMk (contDiff_snd.const_smul (lam m)))).const_smul _
  let B : ℕ → ℕ → ℝ := fun k m => (lam m)⁻¹ ^ m * (Mp m k * lam m ^ k)
  have hB : ∀ k m x, ‖iteratedFDeriv ℝ k (term m) x‖ ≤ B k m := by
    intro k m x
    have hc : ContDiffAt ℝ k (fun y : ReciprocityTheory.L2DbarEstimates.V d × ReciprocityTheory.L2DbarEstimates.V d => g m (y.1, lam m • y.2)) x :=
      ((hgd m).comp (contDiff_fst.prodMk (contDiff_snd.const_smul (lam m)))).contDiffAt.of_le
        (by exact_mod_cast le_top)
    have e1 : iteratedFDeriv ℝ k (term m) x =
        ((lam m)⁻¹ ^ m) • iteratedFDeriv ℝ k (fun y : ReciprocityTheory.L2DbarEstimates.V d × ReciprocityTheory.L2DbarEstimates.V d => g m (y.1, lam m • y.2)) x :=
      iteratedFDeriv_const_smul_apply (a := (lam m)⁻¹ ^ m) hc
    rw [e1, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by have := hlam0 m; positivity)]
    refine mul_le_mul_of_nonneg_left ?_ (by have := hlam0 m; positivity)
    exact norm_iteratedFDeriv_scale_snd (g m) (hgd m) k (Mp m k) (lam m) (hlam1 m)
      (fun y => (hM m k y).trans (le_max_left _ _)) x
  have hB2 : ∀ k m, k < m → B k m ≤ (1 / 2 : ℝ) ^ m := by
    intro k m hkm
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt hkm
    have hl := hlam0 (k + j + 1)
    have hl1 := hlam1 (k + j + 1)
    set L := lam (k + j + 1) with hL
    have e2 : B k (k + j + 1) = Mp (k + j + 1) k * (L⁻¹ ^ (j + 1)) := by
      simp only [B, ← hL]
      rw [show k + j + 1 = k + (j + 1) by ring, pow_add, inv_pow]
      field_simp
    rw [e2]
    have hinv : L⁻¹ ^ (j + 1) ≤ L⁻¹ := pow_le_of_le_one (by positivity) (inv_le_one_of_one_le₀ hl1) (by omega)
    have hmp : 2 ^ (k + j + 1) * Mp (k + j + 1) k ≤ L := by
      have : Mp (k + j + 1) k ≤ ∑ i ∈ Finset.range (k + j + 1), Mp (k + j + 1) i :=
        Finset.single_le_sum (fun i _ => hMp0 _ i) (Finset.mem_range.2 hkm)
      simp only [hL, lam]
      nlinarith [pow_pos (two_pos : (0:ℝ) < 2) (k + j + 1)]
    calc Mp (k + j + 1) k * L⁻¹ ^ (j + 1) ≤ Mp (k + j + 1) k * L⁻¹ :=
          mul_le_mul_of_nonneg_left hinv (hMp0 _ _)
      _ ≤ (1 / 2 : ℝ) ^ (k + j + 1) := by
          rw [← div_eq_mul_inv, div_le_iff₀ hl, one_div, inv_pow]
          rw [inv_mul_eq_div, le_div_iff₀ (by positivity)]
          linarith
  obtain ⟨hfd, hfD⟩ := series_smooth term htd B hB hB2
  refine ⟨fun x => ∑' m, term m x, hfd, ?_⟩
  intro z hz ξ n
  have hterm : ∀ m, iteratedFDeriv ℝ n (term m) (z, 0) (fun _ => ((0 : ReciprocityTheory.L2DbarEstimates.V d), ξ)) =
      if m = n then p n (z, ξ) else 0 := by
    intro m
    rw [← ray_iteratedDeriv (term m) (htd m)]
    have hev : (fun t : ℝ => term m ((z, 0) + t • ((0 : ReciprocityTheory.L2DbarEstimates.V d), ξ))) =ᶠ[𝓝 0]
        fun t : ℝ => t ^ m • (((m.factorial : ℝ))⁻¹ • p m (z, ξ)) := by
      have hcont : Continuous fun t : ℝ => (lam m * t) • ξ := by fun_prop
      have h0 : (fun t : ℝ => (lam m * t) • ξ) 0 = 0 := by simp
      have hmem : ∀ᶠ t in 𝓝 (0 : ℝ), (lam m * t) • ξ ∈ Metric.ball (0 : ReciprocityTheory.L2DbarEstimates.V d) 1 :=
        hcont.continuousAt.preimage_mem_nhds (by simpa using Metric.ball_mem_nhds (0 : ReciprocityTheory.L2DbarEstimates.V d) one_pos)
      filter_upwards [hmem] with t ht
      have hχ : χ ((lam m * t) • ξ) = 1 := χ.one_of_mem_closedBall (Metric.ball_subset_closedBall ht)
      have hρz : ρ z = 1 := hρ1 z (hCO hz)
      have hp' := hhom m z (hCU hz) (lam m * t) ξ
      simp only [term, g, Prod.smul_mk, smul_zero, Prod.mk_add_mk, zero_add, add_zero, smul_smul]
      rw [hρz, hχ, hp']
      try simp only [smul_smul]
      congr 1
      have := (hlam0 m).ne'
      have hf : (m.factorial : ℝ) ≠ 0 := by positivity
      rw [mul_pow, inv_pow]
      field_simp
    rw [hev.iteratedDeriv_eq, iteratedDeriv_pow_smul_zero]
    by_cases h : m = n
    · subst h
      rw [if_pos rfl, if_pos rfl, smul_smul,
        mul_inv_cancel₀ (by exact_mod_cast (Nat.factorial_pos m).ne'), one_smul]
    · rw [if_neg (Ne.symm h), if_neg h]
  have hray : (fun t : ℝ => ∑' m, term m (z, t • ξ)) =
      fun t : ℝ => ∑' m, term m ((z, 0) + t • ((0 : ReciprocityTheory.L2DbarEstimates.V d), ξ)) := by
    funext t; simp [Prod.smul_mk]
  simp only [] at *
  rw [hray, ray_iteratedDeriv _ hfd, hfD]
  simp_rw [hterm]
  rw [tsum_ite_eq]

end GlobalTheory.BorelParam
