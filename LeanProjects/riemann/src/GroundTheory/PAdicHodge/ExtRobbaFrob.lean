import Mathlib
import GroundTheory.PAdicHodge.ExtRobbaBounded
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.PAdicHodge

open Laurent Filter Topology

namespace TeichLift

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ)

theorem teich_eq_of {b : L} {y : Γ}
    (h : ∀ n : ℕ, ∃ z : Γ, T.red z = (((frobeniusEquiv L p).symm : L →+* L))^[n] b ∧
      y - z ^ p ^ n ∈ Ideal.span {T.π ^ (n + 1)}) : T.teich b = y := by
  haveI := T.isAdicComplete
  show Perfection.teichmuller₀ p T.I (T.toPerfection p b) = y
  refine Perfection.teichmuller₀_spec fun n => ?_
  obtain ⟨z, hz, hzy⟩ := h n
  refine ⟨z, ?_, ?_⟩
  · rw [coeff_toPerfection]; exact (T.quotEquiv_symm _ z hz).symm
  · rw [SModEq.sub_mem, T.I_pow, ← neg_sub]; exact neg_mem hzy

theorem ringHom_iterate_frobeniusEquiv_symm (g : L →+* L) (c : L) (n : ℕ) :
    g ((((frobeniusEquiv L p).symm : L →+* L))^[n] c) =
      (((frobeniusEquiv L p).symm : L →+* L))^[n] (g c) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih]
    congr 1
    show g ((frobeniusEquiv L p).symm c) = (frobeniusEquiv L p).symm (g c)
    apply (frobeniusEquiv L p).injective
    rw [RingEquiv.apply_symm_apply, frobeniusEquiv_apply, frobenius_def, ← map_pow,
      frobeniusEquiv_symm_pow_p]

theorem map_teich (ψ : Γ →+* Γ) (g : L →+* L) (hψ : ∀ x, T.red (ψ x) = g (T.red x)) (c : L) :
    ψ (T.teich c) = T.teich (g c) := by
  refine (T.teich_eq_of fun n =>
    ⟨ψ (T.teich ((((frobeniusEquiv L p).symm : L →+* L))^[n] c)), ?_, ?_⟩).symm
  · rw [hψ, red_teich, ringHom_iterate_frobeniusEquiv_symm]
  · rw [← map_pow, ← T.teich_pow, iterate_frobeniusEquiv_symm_pow, sub_self]; exact zero_mem _

theorem gaussNorm_pi_single (k : ℤ) (c : L) {ρ : ℝ} (hρ : 0 < ρ) :
    gaussNorm (Pi.single k c) ρ = ‖c‖ * ρ ^ k := by
  refine le_antisymm (gaussNorm_le fun n => ?_) ?_
  · rw [Pi.single_apply]
    split_ifs with h
    · subst h; exact le_rfl
    · rw [norm_zero, zero_mul]; exact mul_nonneg (norm_nonneg _) (zpow_pos hρ _).le
  · have := (convergesAt_pi_single k c ρ).le_gaussNorm k
    simpa using this

theorem convergesAt_of_mem_int {x : Γ} (hx : x ∈ T.int) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    ConvergesAt (T.zcoeff x) ρ := by
  refine convergesAt_of_eventually hρ0 (T.zcoeff_neg_exists x) fun ε hε => ?_
  obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one hε hρ1
  refine ⟨K, fun n hn => ?_⟩
  lift n to ℕ using (by omega)
  rw [zcoeff_natCast, zpow_natCast]
  calc ‖T.coeff x n‖ * ρ ^ n ≤ 1 * ρ ^ K :=
        mul_le_mul ((T.mem_int_iff.1 hx) n)
          (pow_le_pow_of_le_one hρ0.le hρ1.le (by exact_mod_cast hn)) (by positivity) zero_le_one
    _ ≤ ε := by rw [one_mul]; exact hK.le

theorem gaussNorm_le_one_of_mem_int {x : Γ} (hx : x ∈ T.int) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) :
    gaussNorm (T.zcoeff x) ρ ≤ 1 := by
  refine gaussNorm_le fun n => ?_
  rcases lt_or_ge n 0 with hn | hn
  · rw [T.zcoeff_of_neg _ hn, norm_zero, zero_mul]; exact zero_le_one
  · lift n to ℕ using hn
    rw [zcoeff_natCast, zpow_natCast]
    exact mul_le_one₀ ((T.mem_int_iff.1 hx) n) (by positivity) (pow_le_one₀ hρ0.le hρ1)

theorem gaussNorm_eq_one_of_mem_int {x : Γ} (hx : x ∈ T.int) (h1 : ‖T.red x‖ = 1) {ρ : ℝ}
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) : gaussNorm (T.zcoeff x) ρ = 1 := by
  refine le_antisymm (T.gaussNorm_le_one_of_mem_int hx hρ0 hρ1.le) ?_
  have := T.weight_natCast_le (T.convergesAt_of_mem_int hx hρ0 hρ1) 0
  simpa [h1] using this

theorem exists_inv_mem_int {u : Γ} (hu : u ∈ T.int) (h1 : ‖T.red u‖ = 1) :
    ∃ v ∈ T.int, u * v = 1 := by
  have hu0 : T.red u ≠ 0 := by intro h; rw [h, norm_zero] at h1; exact zero_ne_one h1
  have hr : ‖(T.red u)⁻¹‖ ≤ 1 := by rw [norm_inv, h1, inv_one]
  have hw : T.teich (T.red u)⁻¹ * u ∈ T.int := mul_mem (T.teich_mem_int hr) hu
  have hw1 : T.red (T.teich (T.red u)⁻¹ * u) = 1 := by
    rw [map_mul, red_teich, inv_mul_cancel₀ hu0]
  obtain ⟨s, hs, hws⟩ := T.exists_eq_π_mul (T.teich (T.red u)⁻¹ * u - 1) (sub_mem hw (one_mem _))
    (by rw [map_sub, hw1, map_one, sub_self])
  obtain ⟨v, hv⟩ := (T.isUnit_of_coeff_zero_eq_one (u := T.teich (T.red u)⁻¹ * u)
    (by rw [coeff_zero]; exact hw1)).exists_right_inv
  have hvint : v ∈ T.int := by
    refine T.mem_int_of_approx v fun N => ⟨∑ k ∈ Finset.range N, (-(T.teich (T.red u)⁻¹ * u - 1)) ^ k,
      Subring.sum_mem _ fun k _ => pow_mem (neg_mem (sub_mem hw (one_mem _))) _, ?_⟩
    have hgeom := geom_sum_mul_neg (-(T.teich (T.red u)⁻¹ * u - 1)) N
    rw [show 1 - -(T.teich (T.red u)⁻¹ * u - 1) = T.teich (T.red u)⁻¹ * u by ring] at hgeom
    have : v - ∑ k ∈ Finset.range N, (-(T.teich (T.red u)⁻¹ * u - 1)) ^ k =
        (-(T.teich (T.red u)⁻¹ * u - 1)) ^ N * v := by
      have h2 : (∑ k ∈ Finset.range N, (-(T.teich (T.red u)⁻¹ * u - 1)) ^ k) *
          (T.teich (T.red u)⁻¹ * u) * v = (1 - (-(T.teich (T.red u)⁻¹ * u - 1)) ^ N) * v := by
        rw [hgeom]
      have h3 : (∑ k ∈ Finset.range N, (-(T.teich (T.red u)⁻¹ * u - 1)) ^ k) *
          (T.teich (T.red u)⁻¹ * u) * v = ∑ k ∈ Finset.range N, (-(T.teich (T.red u)⁻¹ * u - 1)) ^ k := by
        rw [mul_assoc, hv, mul_one]
      rw [h3] at h2; rw [h2]; ring
    rw [this, hws]
    exact T.mem_span_pow.2 ⟨(-s) ^ N * v, by ring⟩
  refine ⟨v * T.teich (T.red u)⁻¹, mul_mem hvint (T.teich_mem_int hr), ?_⟩
  calc u * (v * T.teich (T.red u)⁻¹) = (T.teich (T.red u)⁻¹ * u) * v := by ring
    _ = 1 := hv

section Estimate

variable (ψ : Γ →+* Γ) (g : L →+* L) (hψ : ∀ x, T.red (ψ x) = g (T.red x)) {u : Γ}
  (hπ : ψ T.π = T.π * u) (hu : u ∈ T.int) (hu1 : ‖T.red u‖ = 1)

include hψ hπ in
theorem map_partialSum (x : Γ) (N : ℕ) :
    ψ (T.partialSum x N) =
      ∑ m ∈ Finset.range N, T.π ^ m * u ^ m * T.teich (g (T.coeff x m)) := by
  simp only [partialSum, finSum, map_sum, map_mul, map_pow, hπ, T.map_teich ψ g hψ, mul_pow]

include hπ in
theorem map_sub_map_partialSum_mem (x : Γ) (N : ℕ) :
    ψ x - ψ (T.partialSum x N) ∈ Ideal.span {T.π ^ N} := by
  rw [← map_sub, T.sub_partialSum, map_mul, map_pow, hπ, mul_pow, mul_assoc]
  exact T.π_pow_mul_mem le_rfl _

include hu hu1 in
theorem gaussNorm_term {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) (m : ℕ) (c : L) :
    ConvergesAt (T.zcoeff (T.π ^ m * u ^ m * T.teich c)) τ ∧
      gaussNorm (T.zcoeff (T.π ^ m * u ^ m * T.teich c)) τ = τ ^ m * ‖c‖ := by
  have hum : u ^ m ∈ T.int := pow_mem hu m
  have hum1 : ‖T.red (u ^ m)‖ = 1 := by rw [map_pow, norm_pow, hu1, one_pow]
  have c1 : ConvergesAt (T.zcoeff (T.π ^ m)) τ := by
    rw [zcoeff_π_pow]; exact convergesAt_pi_single _ _ _
  have c2 := T.convergesAt_of_mem_int hum hτ0 hτ1
  have c3 : ConvergesAt (T.zcoeff (T.teich c)) τ := by
    rw [zcoeff_teich]; exact convergesAt_pi_single _ _ _
  have c12 := T.convergesAt_zcoeff_mul hτ0 hτ1 c1 c2
  refine ⟨T.convergesAt_zcoeff_mul hτ0 hτ1 c12 c3, ?_⟩
  rw [T.gaussNorm_zcoeff_mul hτ0 hτ1 c12 c3, T.gaussNorm_zcoeff_mul hτ0 hτ1 c1 c2,
    T.gaussNorm_eq_one_of_mem_int hum hum1 hτ0 hτ1, zcoeff_π_pow, zcoeff_teich,
    gaussNorm_pi_single _ _ hτ0, gaussNorm_pi_single _ _ hτ0]
  simp

include hu hu1 in
theorem gaussNorm_sum_terms_le {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) (a : ℕ → L) {B : ℝ}
    (hB : 0 ≤ B) (N : ℕ) (h : ∀ m < N, τ ^ m * ‖a m‖ ≤ B) :
    ConvergesAt (T.zcoeff (∑ m ∈ Finset.range N, T.π ^ m * u ^ m * T.teich (a m))) τ ∧
      gaussNorm (T.zcoeff (∑ m ∈ Finset.range N, T.π ^ m * u ^ m * T.teich (a m))) τ ≤ B := by
  induction N with
  | zero =>
    rw [Finset.sum_range_zero, (T.zcoeff_eq_zero_iff 0).2 rfl]
    exact ⟨convergesAt_zero, by simp [gaussNorm, hB]⟩
  | succ N ih =>
    obtain ⟨ih1, ih2⟩ := ih fun m hm => h m (by omega)
    obtain ⟨t1, t2⟩ := T.gaussNorm_term hu hu1 hτ0 hτ1 N (a N)
    rw [Finset.sum_range_succ]
    exact ⟨T.convergesAt_zcoeff_add hτ0 hτ1 ih1 t1,
      (T.gaussNorm_zcoeff_add_le hτ0 hτ1.le ih1 t1).trans (max_le ih2 (t2 ▸ h N (by omega)))⟩

end Estimate

section Estimate2

variable (ψ : Γ →+* Γ) (g : L →+* L) (hψ : ∀ x, T.red (ψ x) = g (T.red x)) {u : Γ}
  (hπ : ψ T.π = T.π * u) (hu : u ∈ T.int) (hu1 : ‖T.red u‖ = 1) {e : ℝ} (he : 0 < e)
  (hg : ∀ c, ‖g c‖ = ‖c‖ ^ e)

include hg he in
theorem pow_weight_le {σ : ℝ} (hσ0 : 0 < σ) {y : Γ} (hy : ConvergesAt (T.zcoeff y) σ) (m : ℕ) :
    (σ ^ e) ^ m * ‖g (T.coeff y m)‖ ≤ gaussNorm (T.zcoeff y) σ ^ e := by
  have hpow : (σ ^ e) ^ m = (σ ^ m) ^ e := by
    rw [← Real.rpow_natCast (σ ^ e) m, ← Real.rpow_natCast σ m, ← Real.rpow_mul hσ0.le,
      ← Real.rpow_mul hσ0.le, mul_comm]
  rw [hg, hpow, ← Real.mul_rpow (by positivity) (norm_nonneg _)]
  refine Real.rpow_le_rpow (by positivity) ?_ he.le
  have := T.weight_natCast_le hy m
  rwa [zpow_natCast, mul_comm] at this

include hψ hπ hu hu1 he hg in

theorem weight_map_le {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) {y : Γ}
    (hy : ConvergesAt (T.zcoeff y) σ) (n : ℕ) :
    ‖T.coeff (ψ y) n‖ * (σ ^ e) ^ (n : ℤ) ≤ gaussNorm (T.zcoeff y) σ ^ e := by
  have hτ0 : 0 < σ ^ e := Real.rpow_pos_of_pos hσ0 e
  have hτ1 : σ ^ e < 1 := Real.rpow_lt_one hσ0.le hσ1 he
  have hG := gaussNorm_nonneg (a := T.zcoeff y) hσ0
  have hbound : ∀ m < n + 1, (σ ^ e) ^ m * ‖g (T.coeff y m)‖ ≤ gaussNorm (T.zcoeff y) σ ^ e :=
    fun m _ => T.pow_weight_le g he hg hσ0 hy m
  obtain ⟨hc, hle⟩ := T.gaussNorm_sum_terms_le hu hu1 hτ0 hτ1 (fun m => g (T.coeff y m))
    (Real.rpow_nonneg hG e) (n + 1) hbound
  have e1 : T.coeff (ψ y) n = T.coeff (∑ m ∈ Finset.range (n + 1),
      T.π ^ m * u ^ m * T.teich (g (T.coeff y m))) n := by
    rw [← T.map_partialSum ψ g hψ hπ]
    exact T.coeff_eq_coeff_of_sub_mem (T.map_sub_map_partialSum_mem ψ hπ y (n + 1)) n le_rfl
  rw [e1]
  exact (T.weight_natCast_le hc n).trans hle

theorem convergesAt_partialSum {x : Γ} {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (hx : ConvergesAt (T.zcoeff x) σ) (M : ℕ) : ConvergesAt (T.zcoeff (T.partialSum x M)) σ := by
  have := (T.gaussNorm_sum_terms_le (one_mem _) (by simp) hσ0 hσ1 (T.coeff x)
    (gaussNorm_nonneg (a := T.zcoeff x) hσ0) M fun m _ => by
      have := T.weight_natCast_le hx m; rwa [zpow_natCast, mul_comm] at this).1
  simpa [partialSum, finSum] using this

include hψ hπ hu hu1 he hg in

theorem gaussNorm_zcoeff_map_le {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) {x : Γ}
    (hx : ConvergesAt (T.zcoeff x) σ) :
    ConvergesAt (T.zcoeff (ψ x)) (σ ^ e) ∧
      gaussNorm (T.zcoeff (ψ x)) (σ ^ e) ≤ gaussNorm (T.zcoeff x) σ ^ e := by
  have hτ0 : 0 < σ ^ e := Real.rpow_pos_of_pos hσ0 e
  have hτ1 : σ ^ e < 1 := Real.rpow_lt_one hσ0.le hσ1 he
  refine ⟨?_, gaussNorm_le fun n => ?_⟩
  swap
  · rcases lt_or_ge n 0 with hn | hn
    · rw [T.zcoeff_of_neg _ hn, norm_zero, zero_mul]
      exact Real.rpow_nonneg (gaussNorm_nonneg hσ0) e
    · lift n to ℕ using hn
      rw [zcoeff_natCast]
      exact T.weight_map_le ψ g hψ hπ hu hu1 he hg hσ0 hσ1 hx n
  refine convergesAt_of_eventually hτ0 (T.zcoeff_neg_exists _) fun ε hε => ?_
  have hη : 0 < ε ^ (1 / e) := Real.rpow_pos_of_pos hε _
  have hηe : (ε ^ (1 / e)) ^ e = ε := by
    rw [← Real.rpow_mul hε.le, one_div_mul_cancel he.ne', Real.rpow_one]
  obtain ⟨M, hM⟩ : ∃ M : ℕ, ∀ m : ℕ, M ≤ m → ‖T.coeff x m‖ * σ ^ (m : ℤ) ≤ ε ^ (1 / e) := by
    obtain ⟨B, hB⟩ := (hx.finite_le hη).bddAbove
    refine ⟨B.toNat + 1, fun m hm => ?_⟩
    by_contra hc
    push_neg at hc
    have := hB (show (m : ℤ) ∈ {n | ε ^ (1 / e) ≤ ‖T.zcoeff x n‖ * σ ^ n} by
      simp only [Set.mem_setOf_eq, zcoeff_natCast]; exact hc.le)
    omega
  have hPc := T.convergesAt_partialSum hσ0 hσ1 hx M
  have hyc : ConvergesAt (T.zcoeff (x - T.partialSum x M)) σ := by
    rw [sub_eq_add_neg]
    exact T.convergesAt_zcoeff_add hσ0 hσ1 hx (T.convergesAt_zcoeff_neg hσ0 hσ1 hPc)
  have hyG : gaussNorm (T.zcoeff (x - T.partialSum x M)) σ ≤ ε ^ (1 / e) := by
    refine gaussNorm_le fun m => ?_
    rcases lt_or_ge m 0 with hm | hm
    · rw [T.zcoeff_of_neg _ hm, norm_zero, zero_mul]; exact hη.le
    · lift m to ℕ using hm
      rw [zcoeff_natCast, coeff_sub_partialSum]
      split_ifs with h
      · rw [norm_zero, zero_mul]; exact hη.le
      · exact hM m (not_lt.1 h)
  have hA : ConvergesAt (T.zcoeff (ψ (T.partialSum x M))) (σ ^ e) := by
    rw [T.map_partialSum ψ g hψ hπ]
    exact (T.gaussNorm_sum_terms_le hu hu1 hτ0 hτ1 (fun m => g (T.coeff x m))
      (Real.rpow_nonneg (gaussNorm_nonneg hσ0) e) M fun m _ => T.pow_weight_le g he hg hσ0 hx m).1
  obtain ⟨N1, hN1⟩ := exists_prefix_small hτ0 hτ1 hA hε
  refine ⟨max N1 0, fun n hn => ?_⟩
  have hsplit : ψ x = ψ (T.partialSum x M) + ψ (x - T.partialSum x M) := by rw [map_sub]; ring
  have hR : ∀ m ≤ n, ‖T.zcoeff (ψ (x - T.partialSum x M)) m‖ ≤ ε / (σ ^ e) ^ n := by
    intro m hm
    rw [le_div_iff₀ (zpow_pos hτ0 n)]
    rcases lt_or_ge m 0 with hm0 | hm0
    · rw [T.zcoeff_of_neg _ hm0, norm_zero, zero_mul]; exact hε.le
    · lift m to ℕ using hm0
      rw [zcoeff_natCast]
      calc ‖T.coeff (ψ (x - T.partialSum x M)) m‖ * (σ ^ e) ^ n
          ≤ ‖T.coeff (ψ (x - T.partialSum x M)) m‖ * (σ ^ e) ^ (m : ℤ) :=
            mul_le_mul_of_nonneg_left (zpow_le_zpow_right_of_le_one₀ hτ0 hτ1.le hm) (norm_nonneg _)
        _ ≤ gaussNorm (T.zcoeff (x - T.partialSum x M)) σ ^ e :=
            T.weight_map_le ψ g hψ hπ hu hu1 he hg hσ0 hσ1 hyc m
        _ ≤ (ε ^ (1 / e)) ^ e := Real.rpow_le_rpow (gaussNorm_nonneg hσ0) hyG he.le
        _ = ε := hηe
  have := T.norm_zcoeff_add_le (n := n) (div_nonneg hε.le (zpow_pos hτ0 n).le)
    (fun m hm => by
      rw [le_div_iff₀ (zpow_pos hτ0 n)]; exact hN1 n (le_of_max_le_left hn) m hm) hR
  rw [hsplit]
  rwa [le_div_iff₀ (zpow_pos hτ0 n)] at this

end Estimate2

structure TeichFrob (T : TeichLift p L Γ) where

  φ : Γ ≃+* Γ

  a : ℕ
  red_φ : ∀ x, T.red (φ x) = T.red x ^ p ^ a

  u : Γ
  φ_π : φ T.π = T.π * u
  u_mem_int : u ∈ T.int
  norm_red_u : ‖T.red u‖ = 1
  map_int : ∀ x ∈ T.int, φ x ∈ T.int
  symm_map_int : ∀ x ∈ T.int, φ.symm x ∈ T.int

namespace TeichFrob

variable {T} (F : T.TeichFrob)

theorem red_φ' (x : Γ) : T.red (F.φ.toRingHom x) = iterateFrobenius L p F.a (T.red x) := by
  rw [iterateFrobenius_def]; exact F.red_φ x

theorem φ_teich (c : L) : F.φ (T.teich c) = T.teich (c ^ p ^ F.a) := by
  have := T.map_teich F.φ.toRingHom (iterateFrobenius L p F.a) F.red_φ' c
  rwa [iterateFrobenius_def] at this

theorem red_symm (x : Γ) :
    T.red (F.φ.symm x) = (iterateFrobeniusEquiv L p F.a).symm (T.red x) := by
  rw [RingEquiv.eq_symm_apply, iterateFrobeniusEquiv_def, ← F.red_φ, RingEquiv.apply_symm_apply]

theorem norm_iterateFrobenius (c : L) :
    ‖iterateFrobenius L p F.a c‖ = ‖c‖ ^ ((p ^ F.a : ℕ) : ℝ) := by
  rw [iterateFrobenius_def, norm_pow, Real.rpow_natCast]

theorem norm_iterateFrobeniusEquiv_symm (c : L) :
    ‖(iterateFrobeniusEquiv L p F.a).symm c‖ = ‖c‖ ^ (((p ^ F.a : ℕ) : ℝ)⁻¹) := by
  have h := congrArg norm ((iterateFrobeniusEquiv L p F.a).apply_symm_apply c)
  rw [iterateFrobeniusEquiv_def, norm_pow] at h
  rw [← h, Real.pow_rpow_inv_natCast (norm_nonneg _) (pow_ne_zero _ hp.out.ne_zero)]

theorem exists_symm_π :
    ∃ u' ∈ T.int, F.φ.symm T.π = T.π * u' ∧ ‖T.red u'‖ = 1 := by
  have h1 : F.φ.symm T.π ∈ T.int := F.symm_map_int _ T.π_mem_int
  have h2 : T.red (F.φ.symm T.π) = 0 := by rw [F.red_symm, T.red_π, map_zero]
  obtain ⟨u', hu', hπu'⟩ := T.exists_eq_π_mul _ h1 h2
  refine ⟨u', hu', hπu', ?_⟩
  have h3 : T.π * 1 = T.π * (u' * F.φ.symm F.u) := by
    have := congrArg F.φ.symm F.φ_π
    rw [RingEquiv.symm_apply_apply, map_mul, hπu'] at this
    rw [mul_one]; conv_lhs => rw [this]
    ring
  have h4 := T.π_mul_cancel h3
  have h5 := congrArg T.red h4
  rw [map_mul, map_one] at h5
  have n1 := T.norm_red_le_one _ hu'
  have n2 := T.norm_red_le_one _ (F.symm_map_int _ F.u_mem_int)
  have h6 : ‖T.red u'‖ * ‖T.red (F.φ.symm F.u)‖ = 1 := by rw [← norm_mul, ← h5, norm_one]
  refine le_antisymm n1 ?_
  nlinarith [norm_nonneg (T.red u'), norm_nonneg (T.red (F.φ.symm F.u))]

theorem q_pos : 0 < p ^ F.a := pow_pos hp.out.pos _

theorem gaussNorm_zcoeff_map {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) {x : Γ}
    (hx : ConvergesAt (T.zcoeff x) σ) :
    ConvergesAt (T.zcoeff (F.φ x)) (σ ^ p ^ F.a) ∧
      gaussNorm (T.zcoeff (F.φ x)) (σ ^ p ^ F.a) = gaussNorm (T.zcoeff x) σ ^ p ^ F.a := by
  have he : (0 : ℝ) < ((p ^ F.a : ℕ) : ℝ) := by exact_mod_cast F.q_pos
  obtain ⟨h1, h2⟩ := T.gaussNorm_zcoeff_map_le F.φ.toRingHom (iterateFrobenius L p F.a) F.red_φ'
    F.φ_π F.u_mem_int F.norm_red_u he F.norm_iterateFrobenius hσ0 hσ1 hx
  simp only [Real.rpow_natCast, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom] at h1 h2
  refine ⟨h1, le_antisymm h2 ?_⟩
  obtain ⟨u', hu', hπ', hu1'⟩ := F.exists_symm_π
  have hq0 : 0 < σ ^ p ^ F.a := pow_pos hσ0 _
  have hq1 : σ ^ p ^ F.a < 1 := pow_lt_one₀ hσ0.le hσ1 F.q_pos.ne'
  have := (T.gaussNorm_zcoeff_map_le F.φ.symm.toRingHom
    (iterateFrobeniusEquiv L p F.a).symm.toRingHom (fun y => F.red_symm y) hπ' hu' hu1'
    (inv_pos.2 he) F.norm_iterateFrobeniusEquiv_symm hq0 hq1 h1).2
  simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply] at this
  rw [Real.pow_rpow_inv_natCast hσ0.le F.q_pos.ne'] at this
  calc gaussNorm (T.zcoeff x) σ ^ p ^ F.a
      ≤ (gaussNorm (T.zcoeff (F.φ x)) (σ ^ p ^ F.a) ^ (((p ^ F.a : ℕ) : ℝ)⁻¹)) ^ p ^ F.a :=
        pow_le_pow_left₀ (gaussNorm_nonneg hσ0) this _
    _ = gaussNorm (T.zcoeff (F.φ x)) (σ ^ p ^ F.a) := by
        exact Real.rpow_inv_natCast_pow (gaussNorm_nonneg hq0) F.q_pos.ne'

theorem convergesAt_of_map {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) {x : Γ}
    (h : ConvergesAt (T.zcoeff (F.φ x)) (σ ^ p ^ F.a)) : ConvergesAt (T.zcoeff x) σ := by
  have he : (0 : ℝ) < ((p ^ F.a : ℕ) : ℝ) := by exact_mod_cast F.q_pos
  obtain ⟨u', hu', hπ', hu1'⟩ := F.exists_symm_π
  have hq0 : 0 < σ ^ p ^ F.a := pow_pos hσ0 _
  have hq1 : σ ^ p ^ F.a < 1 := pow_lt_one₀ hσ0.le hσ1 F.q_pos.ne'
  have := (T.gaussNorm_zcoeff_map_le F.φ.symm.toRingHom
    (iterateFrobeniusEquiv L p F.a).symm.toRingHom (fun y => F.red_symm y) hπ' hu' hu1'
    (inv_pos.2 he) F.norm_iterateFrobeniusEquiv_symm hq0 hq1 h).1
  simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply] at this
  rwa [Real.pow_rpow_inv_natCast hσ0.le F.q_pos.ne'] at this

theorem isUnit_u : IsUnit F.u := by
  obtain ⟨v, _, hv⟩ := T.exists_inv_mem_int F.u_mem_int F.norm_red_u
  exact ⟨⟨F.u, v, hv, by rw [mul_comm]; exact hv⟩, rfl⟩

theorem isUnit_map_π : IsUnit (((algebraMap Γ T.B).comp F.φ.toRingHom) T.π) := by
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, F.φ_π,
    map_mul]
  exact (IsLocalization.Away.algebraMap_isUnit T.π).mul (F.isUnit_u.map _)

theorem isUnit_map_symm_π : IsUnit (((algebraMap Γ T.B).comp F.φ.symm.toRingHom) T.π) := by
  obtain ⟨u', hu', hπ', hu1'⟩ := F.exists_symm_π
  obtain ⟨v, _, hv⟩ := T.exists_inv_mem_int hu' hu1'
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hπ', map_mul]
  have hu'u : IsUnit u' := ⟨⟨u', v, hv, by rw [mul_comm]; exact hv⟩, rfl⟩
  exact (IsLocalization.Away.algebraMap_isUnit T.π).mul (hu'u.map _)

def toBHom : T.B →+* T.B := IsLocalization.Away.lift T.π F.isUnit_map_π

def toBSymmHom : T.B →+* T.B := IsLocalization.Away.lift T.π F.isUnit_map_symm_π

theorem toBHom_algebraMap (x : Γ) : F.toBHom (algebraMap Γ T.B x) = algebraMap Γ T.B (F.φ x) := by
  rw [toBHom, IsLocalization.Away.lift_eq]; rfl

theorem toBSymmHom_algebraMap (x : Γ) :
    F.toBSymmHom (algebraMap Γ T.B x) = algebraMap Γ T.B (F.φ.symm x) := by
  rw [toBSymmHom, IsLocalization.Away.lift_eq]; rfl

def toB : T.B ≃+* T.B :=
  RingEquiv.ofRingHom F.toBHom F.toBSymmHom
    (IsLocalization.ringHom_ext (Submonoid.powers T.π) (RingHom.ext fun x => by
      simp [toBHom_algebraMap, toBSymmHom_algebraMap]))
    (IsLocalization.ringHom_ext (Submonoid.powers T.π) (RingHom.ext fun x => by
      simp [toBHom_algebraMap, toBSymmHom_algebraMap]))

theorem toB_algebraMap (x : Γ) : F.toB (algebraMap Γ T.B x) = algebraMap Γ T.B (F.φ x) :=
  F.toBHom_algebraMap x

theorem toB_symm_algebraMap (x : Γ) :
    F.toB.symm (algebraMap Γ T.B x) = algebraMap Γ T.B (F.φ.symm x) :=
  F.toBSymmHom_algebraMap x

theorem toB_mul_pow_eq {b : T.B} {x : Γ} {N : ℕ}
    (hb : b * algebraMap Γ T.B T.π ^ N = algebraMap Γ T.B x) {v : Γ} (hv : F.u * v = 1) :
    F.toB b * algebraMap Γ T.B T.π ^ N = algebraMap Γ T.B (F.φ x * v ^ N) := by
  have h1 := congrArg F.toB hb
  rw [map_mul, map_pow, F.toB_algebraMap, F.toB_algebraMap, F.φ_π, map_mul] at h1
  have huv : algebraMap Γ T.B F.u * algebraMap Γ T.B v = 1 := by rw [← map_mul, hv, map_one]
  calc F.toB b * algebraMap Γ T.B T.π ^ N
      = F.toB b * algebraMap Γ T.B T.π ^ N * (algebraMap Γ T.B F.u * algebraMap Γ T.B v) ^ N := by
        rw [huv, one_pow, mul_one]
    _ = (F.toB b * (algebraMap Γ T.B T.π * algebraMap Γ T.B F.u) ^ N) * algebraMap Γ T.B v ^ N := by
        ring
    _ = algebraMap Γ T.B (F.φ x * v ^ N) := by rw [h1, map_mul, map_pow]

theorem exists_inv_u : ∃ v ∈ T.int, F.u * v = 1 ∧ ‖T.red v‖ = 1 := by
  obtain ⟨v, hv, huv⟩ := T.exists_inv_mem_int F.u_mem_int F.norm_red_u
  refine ⟨v, hv, huv, ?_⟩
  have h := congrArg (fun y => ‖T.red y‖) huv
  simp only [map_mul, norm_mul, F.norm_red_u, one_mul, map_one, norm_one] at h
  exact h

theorem convergesAt_coeffB_toB_iff {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (b : T.B) :
    ConvergesAt (T.coeffB (F.toB b)) (σ ^ p ^ F.a) ↔ ConvergesAt (T.coeffB b) σ := by
  obtain ⟨N, x, hx⟩ := IsLocalization.Away.surj T.π b
  obtain ⟨v, hvint, huv, hv1⟩ := F.exists_inv_u
  have hq0 : 0 < σ ^ p ^ F.a := pow_pos hσ0 _
  have hq1 : σ ^ p ^ F.a < 1 := pow_lt_one₀ hσ0.le hσ1 F.q_pos.ne'
  rw [T.coeffB_eq (F.toB_mul_pow_eq hx huv), T.coeffB_eq hx, convergesAt_shift_iff hq0,
    convergesAt_shift_iff hσ0]
  have hvN := T.convergesAt_of_mem_int (pow_mem hvint N) hq0 hq1
  have huN := T.convergesAt_of_mem_int (pow_mem F.u_mem_int N) hq0 hq1
  constructor
  · intro h
    refine F.convergesAt_of_map hσ0 hσ1 ?_
    have := T.convergesAt_zcoeff_mul hq0 hq1 h huN
    rwa [mul_assoc, ← mul_pow, mul_comm v, huv, one_pow, mul_one] at this
  · intro h
    exact T.convergesAt_zcoeff_mul hq0 hq1 (F.gaussNorm_zcoeff_map hσ0 hσ1 h).1 hvN

theorem gaussNorm_coeffB_toB {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) {b : T.B}
    (hb : ConvergesAt (T.coeffB b) σ) :
    gaussNorm (T.coeffB (F.toB b)) (σ ^ p ^ F.a) = gaussNorm (T.coeffB b) σ ^ p ^ F.a := by
  obtain ⟨N, x, hx⟩ := IsLocalization.Away.surj T.π b
  obtain ⟨v, hvint, huv, hv1⟩ := F.exists_inv_u
  have hq0 : 0 < σ ^ p ^ F.a := pow_pos hσ0 _
  have hq1 : σ ^ p ^ F.a < 1 := pow_lt_one₀ hσ0.le hσ1 F.q_pos.ne'
  rw [T.coeffB_eq hx, convergesAt_shift_iff hσ0] at hb
  rw [T.coeffB_eq (F.toB_mul_pow_eq hx huv), T.coeffB_eq hx, gaussNorm_shift hq0,
    gaussNorm_shift hσ0]
  have hvN := T.convergesAt_of_mem_int (pow_mem hvint N) hq0 hq1
  obtain ⟨h1, h2⟩ := F.gaussNorm_zcoeff_map hσ0 hσ1 hb
  have hv1N : ‖T.red (v ^ N)‖ = 1 := by rw [map_pow, norm_pow, hv1, one_pow]
  rw [T.gaussNorm_zcoeff_mul hq0 hq1 h1 hvN, h2,
    T.gaussNorm_eq_one_of_mem_int (pow_mem hvint N) hv1N hq0 hq1, mul_one, mul_pow]
  congr 1
  rw [← zpow_natCast (σ ^ (-(N : ℤ))) (p ^ F.a), ← zpow_mul, ← zpow_natCast σ (p ^ F.a),
    ← zpow_mul, mul_comm]

def powRadius (σ : Set.Ioo (0 : ℝ) 1) : Set.Ioo (0 : ℝ) 1 :=
  ⟨(σ : ℝ) ^ p ^ F.a, pow_pos σ.2.1 _, pow_lt_one₀ σ.2.1.le σ.2.2 F.q_pos.ne'⟩

theorem toB_mem_Econ_iff {σ : Set.Ioo (0 : ℝ) 1} {b : T.B} :
    F.toB b ∈ T.Econ (F.powRadius σ) ↔ b ∈ T.Econ σ :=
  F.convergesAt_coeffB_toB_iff σ.2.1 σ.2.2 b

theorem toB_mem_Edag_iff {b : T.B} : F.toB b ∈ T.Edag ↔ b ∈ T.Edag := by
  constructor
  · rintro ⟨τ, hτ⟩
    let σ : Set.Ioo (0 : ℝ) 1 := ⟨(τ : ℝ) ^ (((p ^ F.a : ℕ) : ℝ)⁻¹), Real.rpow_pos_of_pos τ.2.1 _,
      Real.rpow_lt_one τ.2.1.le τ.2.2 (inv_pos.2 (by exact_mod_cast F.q_pos))⟩
    have hστ : F.powRadius σ = τ :=
      Subtype.ext (Real.rpow_inv_natCast_pow τ.2.1.le F.q_pos.ne')
    exact ⟨σ, F.toB_mem_Econ_iff.1 (hστ ▸ hτ)⟩
  · rintro ⟨σ, hσ⟩
    exact ⟨F.powRadius σ, F.toB_mem_Econ_iff.2 hσ⟩

def edagEquiv : T.Edag ≃+* T.Edag where
  toFun b := ⟨F.toB (b : T.B), F.toB_mem_Edag_iff.2 b.2⟩
  invFun b := ⟨F.toB.symm (b : T.B),
    F.toB_mem_Edag_iff.1 (by rw [RingEquiv.apply_symm_apply]; exact b.2)⟩
  left_inv b := Subtype.ext (F.toB.symm_apply_apply (b : T.B))
  right_inv b := Subtype.ext (F.toB.apply_symm_apply (b : T.B))
  map_mul' b c := Subtype.ext (map_mul F.toB (b : T.B) c)
  map_add' b c := Subtype.ext (map_add F.toB (b : T.B) c)

theorem edagEquiv_apply (b : T.Edag) : (F.edagEquiv b : T.B) = F.toB (b : T.B) := rfl

end TeichFrob

end TeichLift

end GroundTheory.PAdicHodge
