import Mathlib
import GroundTheory.PAdicHodge.SenTateCharLevels
import GroundTheory.PAdicHodge.SenTateCharStep
import GroundTheory.PAdicHodge.SenTateCharClosure
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace SenTateChar

open CyclNorms GroundTheory.LocalField ValuativeRel

variable {p : ℕ} [hp : Fact p.Prime]

instance charP_residueField_intermediateField (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] K] : CharP 𝓀[K] p :=
  charP_residueField_of_valuativeExtension p K

variable {K : IntermediateField ℚ_[p] (PadicAlgCl p)} [FiniteDimensional ℚ_[p] K]
  {η : Gal(PadicAlgCl p/K) →* ℤ_[p]ˣ}

theorem nrm_le_nrm_iff_norm_le' (x y : PadicAlgCl p) : nrm K x ≤ nrm K y ↔ ‖x‖ ≤ ‖y‖ := by
  rw [nrm_le_nrm_iff, vle_iff_norm_le]

theorem nrm_lt_nrm_iff_norm_lt' (x y : PadicAlgCl p) : nrm K x < nrm K y ↔ ‖x‖ < ‖y‖ := by
  rw [← not_le, ← not_le, nrm_le_nrm_iff_norm_le']

theorem restrictNormalHom_mem_lowerRamificationGroup_zero (M : IntermediateField K (PadicAlgCl p))
    [FiniteDimensional K M] [Normal K M] {τ : Gal(PadicAlgCl p/K)} (hτ : τ ∈ inertiaGal K) :
    AlgEquiv.restrictNormalHom M τ ∈ lowerRamificationGroup K M 0 := by
  rw [mem_lowerRamificationGroup_iff_valuation]
  intro x hx
  have hx1 : nrm K ((⟨x, hx⟩ : 𝒪[M]) : PadicAlgCl p) ≤ 1 := (mem_integer_iff_nrm_le_one M x).1 hx
  have hxn : ‖((x : M) : PadicAlgCl p)‖ ≤ 1 := by
    rw [← norm_one (α := PadicAlgCl p), ← nrm_le_nrm_iff_norm_le' (K := K), nrm_one]
    exact hx1
  have h1 := (mem_inertiaGal.1 hτ) _ hxn
  set z : M := AlgEquiv.restrictNormalHom M τ x - x
  have hz : ((z : M) : PadicAlgCl p) = τ (x : PadicAlgCl p) - (x : PadicAlgCl p) := by
    simp only [z, AddSubgroupClass.coe_sub, AlgEquiv.restrictNormalHom_apply]
  have hzlt : nrm K ((z : M) : PadicAlgCl p) < 1 := by
    rw [← nrm_one (K := K) (Ω := PadicAlgCl p), nrm_lt_nrm_iff_norm_lt', norm_one, hz]
    exact h1
  have key : nrm K ((z : M) : PadicAlgCl p) ≤ unifNrm M ^ (1 : ℤ) := by
    rcases eq_or_ne z 0 with h0 | h0
    · rw [h0, IntermediateField.coe_zero, nrm_zero]
      exact le_of_lt (zpow_pos (unifNrm_pos M) _)
    · rw [nrm_eq_unifNrm_zpow M h0] at hzlt ⊢
      have hord : 1 ≤ ord z := by
        by_contra hlt
        push Not at hlt
        have : (1 : ℝ) ≤ unifNrm M ^ ord z :=
          one_le_zpow_of_nonpos₀ (unifNrm_pos M) (unifNrm_lt_one M).le (by omega)
        linarith
      exact zpow_le_zpow_right_of_le_one₀ (unifNrm_pos M) (unifNrm_lt_one M).le hord
  have := (normalizedValuation_le_exp_iff M z 1).2 key
  simpa [z] using this

theorem artinImage_ne_bot (hη : Continuous η) {τ : Gal(PadicAlgCl p/K)} (hτ : τ ∈ inertiaGal K)
    (hτ2 : η τ ∈ unitsOneAdd p 2) (hτ1 : η τ ≠ 1) (n : ℕ) : artinImage K η n ≠ ⊥ := by
  obtain ⟨b, hb, hb'⟩ := exists_level hτ1
  have hb2 : 2 ≤ b := by
    by_contra hlt
    push Not at hlt
    exact hb' (unitsOneAdd_antitone (by omega) hτ2)

  have : FiniteDimensional K (charTower η (b + 1)) := finiteDimensional_charTower hη (b + 1)
  have : IsAbelianGalois K (charTower η (b + 1)) := isAbelianGalois_charTower hη (b + 1)
  have h0 := restrictNormalHom_mem_lowerRamificationGroup_zero (charTower η (b + 1)) hτ
  rw [← upperRamificationGroup_zero, show (0 : ℝ) = ((0 : ℕ) : ℝ) by simp,
    restrictNormalHom_mem_upperRamificationGroup_iff hη, Subgroup.mem_sup] at h0
  obtain ⟨a, ⟨ρ, ⟨u, hu, hu'⟩, rfl⟩, w, hw, haw⟩ := h0
  have ha : η ρ ∈ unitsOneAdd p b := by
    have e : η ρ = η τ * w⁻¹ := by rw [← haw, mul_inv_cancel_right]
    rw [e]
    exact mul_mem hb (inv_mem (unitsOneAdd_antitone (Nat.le_succ b) hw))
  have ha' : η ρ ∉ unitsOneAdd p (b + 1) := fun h => hb' (haw ▸ mul_mem h hw)

  obtain ⟨c, j, hc, hcj⟩ := exists_pow_mem_unitFiltrationUnits (K := K) p n
  have hmem : ρ ^ (c * p ^ j) ∈ artinGal K n := by
    refine ⟨u ^ (c * p ^ j), hcj u hu, ?_⟩
    rw [map_pow, hu', map_pow]
  obtain ⟨h1, h2⟩ := pow_not_mem_of_not_dvd (by omega) ha ha' hc
  obtain ⟨-, h4⟩ := pow_prime_pow_mem_not_mem hb2 h1 h2 j
  intro hbot
  have : η (ρ ^ (c * p ^ j)) ∈ artinImage K η n := ⟨_, hmem, rfl⟩
  rw [hbot, Subgroup.mem_bot, map_pow, pow_mul] at this
  exact h4 (this ▸ one_mem _)

theorem baseUnifNrm_le_one : baseUnifNrm K (PadicAlgCl p) ≤ 1 := by
  rw [← unifNrm_pow_ramificationIndex (⊥ : IntermediateField K (PadicAlgCl p))]
  exact pow_le_one₀ (unifNrm_pos _).le (unifNrm_lt_one _).le

omit [FiniteDimensional ℚ_[p] K] in

theorem div_mul_geom_sum_mul_sub_one (e q : ℕ) :
    (e : ℝ) / p * (∑ i ∈ Finset.range q, (p : ℝ) ^ (-(i : ℤ))) * ((p : ℝ) - 1) =
      e - e * (p : ℝ) ^ (-(q : ℤ)) := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hp1 : (p : ℝ)⁻¹ ≠ 1 := by
    rw [Ne, inv_eq_one]; exact_mod_cast hp.out.one_lt.ne'
  have hr : ∑ i ∈ Finset.range q, (p : ℝ) ^ (-(i : ℤ)) = ∑ i ∈ Finset.range q, ((p : ℝ)⁻¹) ^ i := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [zpow_neg, zpow_natCast, inv_pow]
  rw [hr, geom_sum_eq hp1, zpow_neg, zpow_natCast, inv_pow]
  have hp1' : (p : ℝ)⁻¹ - 1 ≠ 0 := sub_ne_zero.2 hp1
  have hp1'' : (1 : ℝ) - p ≠ 0 := by
    have : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
    linarith
  field_simp
  ring

theorem nrm_normTrace_step_le (hη : Continuous η) (hA : ∀ n, artinImage K η n ≠ ⊥)
    {n' n₀ : ℕ} (hn' : n' ≤ n₀) (h2 : 2 ≤ artinLevel K η n')
    (hper : ∀ n, n₀ ≤ n →
      artinLevel K η (n + absRamificationIndex K) = artinLevel K η n + 1)
    {τ : Gal(PadicAlgCl p/K)} {b : ℕ} (hb2 : 2 ≤ b) (hτb : η τ ∈ unitsOneAdd p b)
    (hτb' : η τ ∉ unitsOneAdd p (b + 1)) {k : ℕ} (hkb : b ≤ k) (hk : artinLevel K η n₀ ≤ k)
    {y : PadicAlgCl p} (hy : y ∈ charTower η (k + 1)) :
    nrm K (normTrace (charTower η k) y) ≤ baseUnifNrm K (PadicAlgCl p) ^
      (-((absRamificationIndex K : ℝ) * (p : ℝ) ^ (-((k - artinLevel K η n₀ : ℕ) : ℤ)))) *
        nrm K y := by
  have : FiniteDimensional K (charTower η (k + 1)) := finiteDimensional_charTower hη (k + 1)
  obtain ⟨hτk, hτk'⟩ := pow_prime_pow_mem_not_mem hb2 hτb hτb' (k - b)
  rw [Nat.add_sub_cancel' hkb] at hτk hτk'
  have hk2 : 2 ≤ k := hb2.trans hkb
  have hητk : η (τ ^ p ^ (k - b)) = η τ ^ p ^ (k - b) := map_pow _ _ _
  have hτM : τ ^ p ^ (k - b) ∈ (charTower η k).fixingSubgroup := by
    rw [fixingSubgroup_charTower hη, mem_charTowerGal, hητk]; exact hτk
  have hτp : (τ ^ p ^ (k - b)) ^ p ∈ (charTower η (k + 1)).fixingSubgroup := by
    rw [fixingSubgroup_charTower hη, mem_charTowerGal, map_pow, hητk]
    exact (pow_prime_mem_iff hk2 hτk).1
  have hτ1 : τ ^ p ^ (k - b) ∉ (charTower η (k + 1)).fixingSubgroup := by
    rw [fixingSubgroup_charTower hη, mem_charTowerGal, hητk]; exact hτk'
  have hgen : ∀ σ ∈ (charTower η k).fixingSubgroup, ∃ j : ℕ,
      ∀ z ∈ charTower η (k + 1), σ z = ((τ ^ p ^ (k - b)) ^ j) z := by
    intro σ hσ
    rw [fixingSubgroup_charTower hη, mem_charTowerGal] at hσ
    obtain ⟨j, hj⟩ := exists_mul_inv_pow_mem hk2 hτk hτk' hσ (k + 1)
    refine ⟨j, fun z hz => ?_⟩
    have hmem : ((τ ^ p ^ (k - b)) ^ j)⁻¹ * σ ∈ (charTower η (k + 1)).fixingSubgroup := by
      rw [fixingSubgroup_charTower hη, mem_charTowerGal, map_mul, map_inv, map_pow, hητk,
        mul_comm]
      exact hj
    have hfix := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hmem z hz
    calc σ z = ((τ ^ p ^ (k - b)) ^ j * (((τ ^ p ^ (k - b)) ^ j)⁻¹ * σ)) z := by
          rw [mul_inv_cancel_left]
      _ = ((τ ^ p ^ (k - b)) ^ j) ((((τ ^ p ^ (k - b)) ^ j)⁻¹ * σ) z) := rfl
      _ = ((τ ^ p ^ (k - b)) ^ j) z := by rw [hfix]
  have hτM' : ∀ z ∈ charTower η (k + 1), (τ ^ p ^ (k - b)) z ∈ charTower η (k + 1) :=
    fun z hz => map_mem_charTower hη _ hz

  have hϖ0 : 0 < baseUnifNrm K (PadicAlgCl p) := baseUnifNrm_pos
  have hϖ1 : baseUnifNrm K (PadicAlgCl p) ≤ 1 := baseUnifNrm_le_one
  set X : ℝ := (absRamificationIndex K : ℝ) / p *
    ∑ i ∈ Finset.range (k - artinLevel K η n₀), (p : ℝ) ^ (-(i : ℤ)) with hXdef
  have hX0 : 0 ≤ X := by positivity
  have hρ0 : 0 ≤ baseUnifNrm K (PadicAlgCl p) ^ X := Real.rpow_nonneg hϖ0.le X
  have hρ1 : baseUnifNrm K (PadicAlgCl p) ^ X ≤ 1 := Real.rpow_le_one hϖ0.le hϖ1 hX0
  have hρ : ∀ z ∈ charTower η (k + 1),
      nrm K ((τ ^ p ^ (k - b)) z - z) ≤ baseUnifNrm K (PadicAlgCl p) ^ X * nrm K z :=
    fun z hz => nrm_sub_le_of_mem_unitsOneAdd hη hA hn' h2 hper hk (by rw [hητk]; exact hτk) hz
  have h := nrm_normTrace_mul_le (M := charTower η k) (M' := charTower η (k + 1))
    (hMM' := charTower_mono η (Nat.le_succ k)) (hτM := hτM) (hτp := hτp) (hτ1 := hτ1)
    (hgen := hgen) (hτM' := hτM') (hρ0 := hρ0) (hρ1 := hρ1) (hρ := hρ) (hy := hy)

  have hp1 : 1 ≤ p := hp.out.one_lt.le
  have hpe : nrm K (p : PadicAlgCl p) =
      baseUnifNrm K (PadicAlgCl p) ^ (absRamificationIndex K : ℝ) := by
    rw [nrm_natCast_prime_eq p, Real.rpow_natCast]
  have hρp : (baseUnifNrm K (PadicAlgCl p) ^ X) ^ (p - 1) =
      baseUnifNrm K (PadicAlgCl p) ^ (absRamificationIndex K : ℝ) *
        baseUnifNrm K (PadicAlgCl p) ^ (-((absRamificationIndex K : ℝ) *
          (p : ℝ) ^ (-((k - artinLevel K η n₀ : ℕ) : ℤ)))) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hϖ0.le, ← Real.rpow_add hϖ0]
    congr 1
    rw [Nat.cast_sub hp1, Nat.cast_one, hXdef, div_mul_geom_sum_mul_sub_one]
    ring
  have hone : 1 ≤ baseUnifNrm K (PadicAlgCl p) ^ (-((absRamificationIndex K : ℝ) *
      (p : ℝ) ^ (-((k - artinLevel K η n₀ : ℕ) : ℤ)))) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hϖ0 hϖ1 (by
      have : 0 ≤ (absRamificationIndex K : ℝ) * (p : ℝ) ^ (-((k - artinLevel K η n₀ : ℕ) : ℤ)) := by
        positivity
      linarith)
  have hmax : max (nrm K (p : PadicAlgCl p)) ((baseUnifNrm K (PadicAlgCl p) ^ X) ^ (p - 1)) ≤
      nrm K (p : PadicAlgCl p) * baseUnifNrm K (PadicAlgCl p) ^ (-((absRamificationIndex K : ℝ) *
        (p : ℝ) ^ (-((k - artinLevel K η n₀ : ℕ) : ℤ)))) := by
    refine max_le (le_mul_of_one_le_right (nrm_nonneg _) hone) ?_
    rw [hρp, hpe]
  have hpos : 0 < nrm K (p : PadicAlgCl p) :=
    nrm_pos.2 (Nat.cast_ne_zero.2 hp.out.ne_zero)
  have h3 := h.trans (mul_le_mul_of_nonneg_right hmax (nrm_nonneg _))
  rw [mul_comm (nrm K (normTrace (charTower η k) y)), mul_assoc] at h3
  exact le_of_mul_le_mul_left h3 hpos

omit [FiniteDimensional ℚ_[p] K] in

theorem sum_zpow_neg_le (j : ℕ) :
    ∑ i ∈ Finset.range j, (p : ℝ) ^ (-(i : ℤ)) ≤ 2 - 2 * (p : ℝ) ^ (-(j : ℤ)) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.out.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Finset.sum_range_succ]
    have e : (p : ℝ) ^ (-((j + 1 : ℕ) : ℤ)) = (p : ℝ) ^ (-(j : ℤ)) * (p : ℝ)⁻¹ := by
      rw [← zpow_neg_one, ← zpow_add₀ hp0.ne']; congr 1; push_cast; ring
    rw [e]
    have hq : 0 ≤ (p : ℝ) ^ (-(j : ℤ)) := by positivity
    have hinv : (p : ℝ)⁻¹ ≤ 1 / 2 := by
      rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) hp2
    nlinarith

theorem nrm_normTrace_charTower_le (hη : Continuous η) (hA : ∀ n, artinImage K η n ≠ ⊥)
    {n' n₀ : ℕ} (hn' : n' ≤ n₀) (h2 : 2 ≤ artinLevel K η n')
    (hper : ∀ n, n₀ ≤ n →
      artinLevel K η (n + absRamificationIndex K) = artinLevel K η n + 1)
    {τ : Gal(PadicAlgCl p/K)} {b : ℕ} (hb2 : 2 ≤ b) (hτb : η τ ∈ unitsOneAdd p b)
    (hτb' : η τ ∉ unitsOneAdd p (b + 1)) {n : ℕ} (hnb : b ≤ n) (hn : artinLevel K η n₀ ≤ n)
    {m : ℕ} {y : PadicAlgCl p} (hy : y ∈ charTower η m) :
    nrm K (normTrace (charTower η n) y) ≤
      baseUnifNrm K (PadicAlgCl p) ^ (-(2 * absRamificationIndex K : ℝ)) * nrm K y := by
  have hfin : ∀ k, FiniteDimensional K (charTower η k) := fun k => finiteDimensional_charTower hη k
  have hϖ0 : 0 < baseUnifNrm K (PadicAlgCl p) := baseUnifNrm_pos
  have hϖ1 : baseUnifNrm K (PadicAlgCl p) ≤ 1 := baseUnifNrm_le_one
  have hone : 1 ≤ baseUnifNrm K (PadicAlgCl p) ^ (-(2 * absRamificationIndex K : ℝ)) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hϖ0 hϖ1 (by
      have : (0 : ℝ) ≤ 2 * absRamificationIndex K := by positivity
      linarith)
  rcases le_total m n with hmn | hnm
  · rw [normTrace_of_mem _ (charTower_mono η hmn hy)]
    exact le_mul_of_one_le_left (nrm_nonneg _) hone
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hnm

  have hclaim : ∀ j, ∀ z ∈ charTower η (n + j), nrm K (normTrace (charTower η n) z) ≤
      baseUnifNrm K (PadicAlgCl p) ^ (-(∑ i ∈ Finset.range j, (absRamificationIndex K : ℝ) *
        (p : ℝ) ^ (-((n + i - artinLevel K η n₀ : ℕ) : ℤ)))) * nrm K z := by
    intro j
    induction j with
    | zero =>
      intro z hz
      rw [add_zero] at hz
      rw [normTrace_of_mem _ hz]
      simp
    | succ j ih =>
      intro z hz
      have hz' : normTrace (charTower η (n + j)) z ∈ charTower η (n + j) := normTrace_mem _ z
      have hcomp : normTrace (charTower η n) (normTrace (charTower η (n + j)) z) =
          normTrace (charTower η n) z :=
        normTrace_normTrace_of_le (charTower_mono η (Nat.le_add_right n j)) z
      have hstep := nrm_normTrace_step_le hη hA hn' h2 hper hb2 hτb hτb'
        (show b ≤ n + j by omega) (show artinLevel K η n₀ ≤ n + j by omega)
        (show z ∈ charTower η (n + j + 1) by simpa [add_assoc] using hz)
      rw [← hcomp]
      refine (ih _ hz').trans ?_
      rw [Finset.sum_range_succ, neg_add, Real.rpow_add hϖ0, mul_assoc]
      exact mul_le_mul_of_nonneg_left hstep (Real.rpow_nonneg hϖ0.le _)
  refine (hclaim j y hy).trans (mul_le_mul_of_nonneg_right ?_ (nrm_nonneg _))
  refine Real.rpow_le_rpow_of_exponent_ge hϖ0 hϖ1 (neg_le_neg ?_)
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.out.one_lt.le
  calc ∑ i ∈ Finset.range j, (absRamificationIndex K : ℝ) *
        (p : ℝ) ^ (-((n + i - artinLevel K η n₀ : ℕ) : ℤ))
      ≤ ∑ i ∈ Finset.range j, (absRamificationIndex K : ℝ) * (p : ℝ) ^ (-(i : ℤ)) := by
        refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
        exact zpow_le_zpow_right₀ hp1 (by omega)
    _ = (absRamificationIndex K : ℝ) * ∑ i ∈ Finset.range j, (p : ℝ) ^ (-(i : ℤ)) := by
        rw [Finset.mul_sum]
    _ ≤ (absRamificationIndex K : ℝ) * 2 := by
        refine mul_le_mul_of_nonneg_left ((sum_zpow_neg_le j).trans ?_) (Nat.cast_nonneg _)
        have : 0 ≤ (p : ℝ) ^ (-(j : ℤ)) := by positivity
        linarith
    _ = 2 * absRamificationIndex K := by ring

end SenTateChar

end GroundTheory.PAdicHodge
