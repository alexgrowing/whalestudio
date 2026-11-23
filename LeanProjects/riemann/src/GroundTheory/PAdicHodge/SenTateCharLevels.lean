import Mathlib
import GroundTheory.PAdicHodge.SenTateCharTower
import GroundTheory.PAdicHodge.SenTateCharUnitPow
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace SenTateChar

open CyclNorms GroundTheory.LocalField ValuativeRel

variable {p : ℕ} [hp : Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}
  [FiniteDimensional ℚ_[p] K] {η : Gal(PadicAlgCl p/K) →* ℤ_[p]ˣ}

instance valuativeExtension_charTower (k : ℕ) : ValuativeExtension K (charTower η k) :=
  GroundTheory.LocalField.intermediateField_valuativeExtension_left _

variable (K η) in

def artinLevel (n : ℕ) : ℕ := sInf {k | ¬ artinImage K η n ≤ unitsOneAdd p (k + 1)}

theorem artinLevel_spec {n : ℕ} (h : artinImage K η n ≠ ⊥) :
    artinImage K η n ≤ unitsOneAdd p (artinLevel K η n) ∧
      ∃ a ∈ artinImage K η n, a ∉ unitsOneAdd p (artinLevel K η n + 1) := by
  have hne : {k | ¬ artinImage K η n ≤ unitsOneAdd p (k + 1)}.Nonempty := by
    obtain ⟨a, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 h
    obtain ⟨s, -, hs'⟩ := exists_level (p := p) (a := (a : ℤ_[p]ˣ)) (fun h' => ha1 (Subtype.ext h'))
    exact ⟨s, fun hle => hs' (hle a.2)⟩
  have hmem := Nat.sInf_mem hne
  refine ⟨?_, ?_⟩
  · rcases Nat.eq_zero_or_eq_succ_pred (artinLevel K η n) with h0 | h0
    · rw [h0, unitsOneAdd_zero]; exact le_top
    · have hlt : Nat.pred (artinLevel K η n) < artinLevel K η n := by omega
      have := Nat.notMem_of_lt_sInf hlt
      simp only [Set.mem_ofPred_eq, not_not] at this
      rw [h0]
      exact this
  · have hmem' : ¬ artinImage K η n ≤ unitsOneAdd p (artinLevel K η n + 1) := hmem
    exact SetLike.not_le_iff_exists.1 hmem'

theorem artinLevel_mono (hA : ∀ n, artinImage K η n ≠ ⊥) : Monotone (artinLevel K η) := by
  intro n n' hnn'
  obtain ⟨-, a, ha, ha'⟩ := artinLevel_spec (hA n')
  have h1 := (artinLevel_spec (hA n)).1 (artinImage_antitone η hnn' ha)
  by_contra hlt
  push Not at hlt
  exact ha' (unitsOneAdd_antitone (by omega) h1)

theorem artinLevel_add (hη : Continuous η) (hA : ∀ n, artinImage K η n ≠ ⊥) {n e : ℕ}
    (h2 : 2 ≤ artinLevel K η n)
    (hpow : (unitFiltrationUnits K n).map (powMonoidHom p) = unitFiltrationUnits K (n + e)) :
    artinLevel K η (n + e) = artinLevel K η n + 1 := by
  have heq := artinImage_add_eq_map_pow hη hpow
  obtain ⟨hle, a, ha, ha'⟩ := artinLevel_spec (hA n)
  obtain ⟨hle', b, hb, hb'⟩ := artinLevel_spec (hA (n + e))
  apply le_antisymm
  ·
    have hap : a ^ p ∈ artinImage K η (n + e) := by rw [heq]; exact ⟨a, ha, rfl⟩
    have hap' : a ^ p ∉ unitsOneAdd p (artinLevel K η n + 2) := fun h =>
      ha' (((pow_prime_mem_iff h2 (hle ha)).2).1 h)
    by_contra hlt
    push Not at hlt
    exact hap' (unitsOneAdd_antitone (by omega) (hle' hap))
  ·
    have hle2 : artinImage K η (n + e) ≤ unitsOneAdd p (artinLevel K η n + 1) := by
      rw [heq]
      rintro _ ⟨c, hc, rfl⟩
      exact (pow_prime_mem_iff h2 (hle hc)).1
    by_contra hlt
    push Not at hlt
    exact hb' (unitsOneAdd_antitone (by omega) (hle2 hb))

theorem artinImage_sup_unitsOneAdd {n : ℕ} (hA : artinImage K η n ≠ ⊥) (h2 : 2 ≤ artinLevel K η n)
    (k : ℕ) : artinImage K η n ⊔ unitsOneAdd p k = unitsOneAdd p (min (artinLevel K η n) k) := by
  obtain ⟨hle, a, ha, ha'⟩ := artinLevel_spec hA
  apply le_antisymm
  · exact sup_le (hle.trans (unitsOneAdd_antitone (min_le_left _ _)))
      (unitsOneAdd_antitone (min_le_right _ _))
  · intro b hb
    rcases le_total k (artinLevel K η n) with hk | hk
    · rw [min_eq_right hk] at hb
      exact Subgroup.mem_sup_right hb
    · rw [min_eq_left hk] at hb
      obtain ⟨j, hj⟩ := exists_mul_inv_pow_mem h2 (hle ha) ha' hb k
      have e : b = a ^ j * (b * (a ^ j)⁻¹) := by rw [mul_comm, inv_mul_cancel_right]
      rw [e]
      exact Subgroup.mul_mem_sup (pow_mem ha j) hj

theorem restrictNormalHom_mem_upperRamificationGroup_iff_level (hη : Continuous η) {k n : ℕ}
    (hA : artinImage K η n ≠ ⊥) (h2 : 2 ≤ artinLevel K η n)
    [FiniteDimensional K (charTower η k)] [IsAbelianGalois K (charTower η k)]
    (σ : Gal(PadicAlgCl p/K)) :
    AlgEquiv.restrictNormalHom (charTower η k) σ ∈ upperRamificationGroup K (charTower η k) n ↔
      η σ ∈ unitsOneAdd p (min (artinLevel K η n) k) := by
  rw [restrictNormalHom_mem_upperRamificationGroup_iff hη, artinImage_sup_unitsOneAdd hA h2]

theorem upperRamificationGroup_charTower_eq_map (hη : Continuous η) {k n : ℕ}
    (hA : artinImage K η n ≠ ⊥) (h2 : 2 ≤ artinLevel K η n)
    [FiniteDimensional K (charTower η k)] [IsAbelianGalois K (charTower η k)] :
    upperRamificationGroup K (charTower η k) n =
      (charTowerGal η (min (artinLevel K η n) k)).map
        (AlgEquiv.restrictNormalHom (charTower η k)) := by
  ext g
  obtain ⟨σ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := charTower η k)
    (E := PadicAlgCl p) g
  rw [restrictNormalHom_mem_upperRamificationGroup_iff_level hη hA h2]
  constructor
  · intro h
    exact ⟨σ, h, rfl⟩
  · rintro ⟨σ', hσ', heq⟩
    have h1 : AlgEquiv.restrictNormalHom (charTower η k) (σ'⁻¹ * σ) = 1 := by
      rw [map_mul, map_inv, heq, inv_mul_cancel]
    have h2' := (restrictNormalHom_charTower_eq_one_iff hη k _).1 h1
    have e : η σ = η σ' * η (σ'⁻¹ * σ) := by rw [map_mul, map_inv, mul_inv_cancel_left]
    rw [e]
    exact mul_mem hσ' (unitsOneAdd_antitone (min_le_right _ _) h2')

omit [FiniteDimensional ℚ_[p] K] in

theorem relIndex_charTowerGal {s t : ℕ} (hs : 2 ≤ s) (hst : s ≤ t) {a : ℤ_[p]ˣ} (haR : a ∈ η.range)
    (ha : a ∈ unitsOneAdd p s) (ha' : a ∉ unitsOneAdd p (s + 1)) :
    (charTowerGal η t).relIndex (charTowerGal η s) = p ^ (t - s) := by
  rw [charTowerGal, charTowerGal, Subgroup.relIndex_comap, Subgroup.map_comap_eq,
    ← Subgroup.inf_relIndex_right, inf_comm η.range, ← inf_assoc,
    inf_eq_left.2 (unitsOneAdd_antitone hst)]
  have h := relIndex_unitsOneAdd_inf hs η.range haR ha ha' (t - s)
  rwa [Nat.add_sub_cancel' hst] at h

theorem relIndex_upperRamificationGroup_charTower (hη : Continuous η)
    (hA : ∀ n, artinImage K η n ≠ ⊥) {k n' j : ℕ} (hn'j : n' ≤ j) (h2 : 2 ≤ artinLevel K η n')
    (hjk : artinLevel K η j ≤ k)
    [FiniteDimensional K (charTower η k)] [IsAbelianGalois K (charTower η k)] :
    (upperRamificationGroup K (charTower η k) j).relIndex
        (upperRamificationGroup K (charTower η k) n') =
      p ^ (artinLevel K η j - artinLevel K η n') := by
  have hmono := artinLevel_mono hA hn'j
  have h2j : 2 ≤ artinLevel K η j := h2.trans hmono
  rw [upperRamificationGroup_charTower_eq_map hη (hA j) h2j,
    upperRamificationGroup_charTower_eq_map hη (hA n') h2, Subgroup.relIndex_map_map,
    (charTower η k).restrictNormalHom_ker, fixingSubgroup_charTower hη, min_eq_left hjk,
    min_eq_left (hmono.trans hjk), sup_eq_left.2 (charTowerGal_antitone η hjk),
    sup_eq_left.2 (charTowerGal_antitone η (hmono.trans hjk))]
  obtain ⟨hle, a, ha, ha'⟩ := artinLevel_spec (hA n')
  exact relIndex_charTowerGal h2 hmono (Subgroup.map_le_range η _ ha) (hle ha) ha'

theorem card_upperRamificationGroup_charTower (hη : Continuous η)
    (hA : ∀ n, artinImage K η n ≠ ⊥) {k n' : ℕ} (h2 : 2 ≤ artinLevel K η n')
    (hk : artinLevel K η n' ≤ k)
    [FiniteDimensional K (charTower η k)] [IsAbelianGalois K (charTower η k)] :
    Nat.card (upperRamificationGroup K (charTower η k) n') = p ^ (k - artinLevel K η n') := by
  rw [upperRamificationGroup_charTower_eq_map hη (hA n') h2, min_eq_left hk,
    ← Subgroup.relIndex_bot_left, ← Subgroup.relIndex_comap, MonoidHom.comap_bot,
    (charTower η k).restrictNormalHom_ker, fixingSubgroup_charTower hη]
  obtain ⟨hle, a, ha, ha'⟩ := artinLevel_spec (hA n')
  exact relIndex_charTowerGal h2 hk (Subgroup.map_le_range η _ ha) (hle ha) ha'

theorem integral_eq_sum_of_eq_ceil {f : ℝ → ℝ} (hf : ∀ w, f w = f (⌈w⌉ : ℝ))
    (hint : ∀ a b : ℝ, IntervalIntegrable f MeasureTheory.volume a b) (N : ℕ) :
    ∫ w in (0 : ℝ)..N, f w = ∑ j ∈ Finset.Ioc 0 N, f j := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Ioc_succ_top (Nat.zero_le N), ← ih,
      ← intervalIntegral.integral_add_adjacent_intervals (hint 0 N) (hint N ((N + 1 : ℕ) : ℝ))]
    congr 1
    have hc : ∫ w in (N : ℝ)..((N + 1 : ℕ) : ℝ), f w =
        ∫ _ in (N : ℝ)..((N + 1 : ℕ) : ℝ), f ((N + 1 : ℕ) : ℝ) := by
      refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun w hw => ?_)
      have hle : (N : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ N
      rw [Set.uIoc_of_le hle] at hw
      rw [hf w]
      congr 1
      have : ⌈w⌉ = ((N + 1 : ℕ) : ℤ) := by
        rw [Int.ceil_eq_iff]
        push_cast at hw ⊢
        constructor <;> linarith [hw.1, hw.2]
      rw [this]
      norm_cast
    rw [Nat.cast_succ] at hc ⊢
    rw [hc, intervalIntegral.integral_const, smul_eq_mul]
    ring

theorem sum_zpow_block_le (μ : ℕ → ℕ) (hμ : Monotone μ) {e n₀ : ℕ}
    (hper : ∀ n, n₀ ≤ n → μ (n + e) = μ n + 1) {N k : ℕ} (hN : k + 1 ≤ μ (N + 1)) {b : ℝ}
    (hb : 1 ≤ b) : ∀ q : ℕ, n₀ + e * q ≤ N →
      (e : ℝ) * ∑ i ∈ Finset.range q, b ^ ((k : ℤ) - i) ≤
        ∑ j ∈ Finset.Ioc (N - e * q) N, b ^ (μ j : ℤ)
  | 0, _ => by simp
  | q + 1, hq => by
    rw [show e * (q + 1) = e * q + e by ring] at hq ⊢
    have ih := sum_zpow_block_le μ hμ hper hN hb q (by omega)

    have hiter : ∀ i j, n₀ ≤ j → μ (j + e * i) = μ j + i := by
      intro i
      induction i with
      | zero => simp
      | succ i ihi =>
        intro j hj
        rw [mul_add, mul_one, ← add_assoc, hper _ (by omega), ihi j hj, add_assoc]
    have hsplit : Finset.Ioc (N - (e * q + e)) N =
        Finset.Ioc (N - (e * q + e)) (N - e * q) ∪ Finset.Ioc (N - e * q) N := by
      rw [Finset.Ioc_union_Ioc_eq_Ioc (by omega) (by omega)]
    have hdisj : Disjoint (Finset.Ioc (N - (e * q + e)) (N - e * q)) (Finset.Ioc (N - e * q) N) :=
      Finset.Ioc_disjoint_Ioc_of_le le_rfl
    rw [hsplit, Finset.sum_union hdisj, Finset.sum_range_succ, mul_add, add_comm]
    refine add_le_add ?_ ih

    have hcard : (Finset.Ioc (N - (e * q + e)) (N - e * q)).card = e := by
      rw [Nat.card_Ioc]; omega
    calc (e : ℝ) * b ^ ((k : ℤ) - q)
        = ∑ _j ∈ Finset.Ioc (N - (e * q + e)) (N - e * q), b ^ ((k : ℤ) - q) := by
          rw [Finset.sum_const, hcard, nsmul_eq_mul]
      _ ≤ ∑ j ∈ Finset.Ioc (N - (e * q + e)) (N - e * q), b ^ (μ j : ℤ) := by
          refine Finset.sum_le_sum fun j hj => ?_
          rw [Finset.mem_Ioc] at hj
          refine zpow_le_zpow_right₀ hb ?_

          have h1 : μ (j + e * q) = μ j + q := hiter q j (by omega)
          have h2 : k + 1 ≤ μ (j + e * q + e) := hN.trans (hμ (by omega))
          rw [hper _ (by omega), h1] at h2
          omega

theorem artinLevel_add_mul {n₀ e : ℕ}
    (hper : ∀ n, n₀ ≤ n → artinLevel K η (n + e) = artinLevel K η n + 1) (i : ℕ) :
    artinLevel K η (n₀ + e * i) = artinLevel K η n₀ + i := by
  induction i with
  | zero => simp
  | succ i ih => rw [mul_add, mul_one, ← add_assoc, hper _ (by omega), ih, add_assoc]

theorem exists_last_artinLevel_le (hA : ∀ n, artinImage K η n ≠ ⊥) {n₀ e : ℕ}
    (hper : ∀ n, n₀ ≤ n → artinLevel K η (n + e) = artinLevel K η n + 1) {k : ℕ}
    (hk : artinLevel K η n₀ ≤ k) :
    ∃ N, artinLevel K η N ≤ k ∧ k + 1 ≤ artinLevel K η (N + 1) ∧
      n₀ + e * (k - artinLevel K η n₀) ≤ N := by
  have hmono := artinLevel_mono hA
  have hiter := artinLevel_add_mul hper
  have hex : ∃ n, k < artinLevel K η n :=
    ⟨n₀ + e * (k - artinLevel K η n₀ + 1), by rw [hiter]; omega⟩
  classical
  have hF : k < artinLevel K η (Nat.find hex) := Nat.find_spec hex
  have hF0 : Nat.find hex ≠ 0 := by
    intro h0
    rw [h0] at hF
    have := hmono (Nat.zero_le n₀)
    omega
  obtain ⟨N, hNF⟩ : ∃ N, N + 1 = Nat.find hex := ⟨Nat.find hex - 1, by omega⟩
  refine ⟨N, ?_, by rw [hNF]; exact hF, ?_⟩
  · have := Nat.find_min hex (show N < Nat.find hex by omega)
    omega
  · by_contra hlt
    push Not at hlt
    have := hmono (show Nat.find hex ≤ n₀ + e * (k - artinLevel K η n₀) by omega)
    rw [hiter] at this
    omega

theorem le_herbrandPsi_div_ramificationIndex (hη : Continuous η) (hA : ∀ n, artinImage K η n ≠ ⊥)
    {n' n₀ e : ℕ} (hn' : n' ≤ n₀) (h2 : 2 ≤ artinLevel K η n')
    (hper : ∀ n, n₀ ≤ n → artinLevel K η (n + e) = artinLevel K η n + 1)
    {k N : ℕ} (hNk : artinLevel K η N ≤ k) (hN1 : k + 1 ≤ artinLevel K η (N + 1))
    (hNq : n₀ + e * (k - artinLevel K η n₀) ≤ N)
    [FiniteDimensional K (charTower η (k + 1))] [IsAbelianGalois K (charTower η (k + 1))] :
    (e : ℝ) / p * ∑ i ∈ Finset.range (k - artinLevel K η n₀), (p : ℝ) ^ (-(i : ℤ)) ≤
      herbrandPsi K (charTower η (k + 1)) N / ramificationIndex K (charTower η (k + 1)) := by
  have hmono := artinLevel_mono hA
  have hn'N : n' ≤ N := le_trans hn' (le_trans (Nat.le_add_right _ _) hNq)
  have hsk : artinLevel K η n' ≤ k := (hmono hn'N).trans hNk

  have hn'0 : upperRamificationGroup K (charTower η (k + 1)) n' ≤
      lowerRamificationGroup K (charTower η (k + 1)) 0 := by
    rw [← upperRamificationGroup_zero]
    exact upperRamificationGroup_antitone K _ (Nat.cast_nonneg n')
  obtain ⟨c, hc⟩ : ∃ c, (upperRamificationGroup K (charTower η (k + 1)) n').relIndex
      (lowerRamificationGroup K (charTower η (k + 1)) 0) = c := ⟨_, rfl⟩
  have hE : ramificationIndex K (charTower η (k + 1)) = c * p ^ (k + 1 - artinLevel K η n') := by
    rw [← card_lowerRamificationGroup_zero, ← Subgroup.relIndex_bot_left,
      ← Subgroup.relIndex_mul_relIndex _ _ _ bot_le hn'0, Subgroup.relIndex_bot_left,
      card_upperRamificationGroup_charTower hη hA h2 (by omega), hc, mul_comm]

  have hψsum : herbrandPsi K (charTower η (k + 1)) N =
      ∑ j ∈ Finset.Ioc 0 N, (upperIndex K (charTower η (k + 1)) j : ℝ) := by
    rw [herbrandPsi_eq_integral (Nat.cast_nonneg N)]
    refine integral_eq_sum_of_eq_ceil (fun w => ?_) (fun a b => intervalIntegrable_upperIndex a b) N
    simp only [upperIndex]
    rw [upperRamificationGroup_eq_ceil (L := charTower η (k + 1)) w]
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.out.one_lt.le
  have hp0 : (0 : ℝ) < p := by linarith
  have hterm : ∀ j ∈ Finset.Ioc (N - e * (k - artinLevel K η n₀)) N,
      (upperIndex K (charTower η (k + 1)) j : ℝ) =
        (c : ℝ) * (p : ℝ) ^ (-(artinLevel K η n' : ℤ)) * (p : ℝ) ^ (artinLevel K η j : ℤ) := by
    intro j hj
    rw [Finset.mem_Ioc] at hj
    have hn'j : n' ≤ j := by omega
    have hjk : artinLevel K η j ≤ k + 1 := by have := hmono hj.2; omega
    have hsj : artinLevel K η n' ≤ artinLevel K η j := hmono hn'j
    rw [upperIndex, ← Subgroup.relIndex_mul_relIndex _ _ _
      (upperRamificationGroup_antitone K _ (by exact_mod_cast hn'j)) hn'0,
      relIndex_upperRamificationGroup_charTower hη hA hn'j h2 hjk, hc]
    push_cast
    rw [← zpow_natCast, Nat.cast_sub hsj, zpow_sub₀ hp0.ne', zpow_neg]
    ring
  have hψlow : (c : ℝ) * (p : ℝ) ^ (-(artinLevel K η n' : ℤ)) *
      ((e : ℝ) * ∑ i ∈ Finset.range (k - artinLevel K η n₀), (p : ℝ) ^ ((k : ℤ) - i)) ≤
        herbrandPsi K (charTower η (k + 1)) N := by
    rw [hψsum]
    calc (c : ℝ) * (p : ℝ) ^ (-(artinLevel K η n' : ℤ)) *
          ((e : ℝ) * ∑ i ∈ Finset.range (k - artinLevel K η n₀), (p : ℝ) ^ ((k : ℤ) - i))
        ≤ (c : ℝ) * (p : ℝ) ^ (-(artinLevel K η n' : ℤ)) *
            ∑ j ∈ Finset.Ioc (N - e * (k - artinLevel K η n₀)) N, (p : ℝ) ^ (artinLevel K η j : ℤ) :=
          mul_le_mul_of_nonneg_left
            (sum_zpow_block_le (artinLevel K η) hmono hper hN1 hp1 _ hNq) (by positivity)
      _ = ∑ j ∈ Finset.Ioc (N - e * (k - artinLevel K η n₀)) N,
            (upperIndex K (charTower η (k + 1)) j : ℝ) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j hj => (hterm j hj).symm
      _ ≤ ∑ j ∈ Finset.Ioc 0 N, (upperIndex K (charTower η (k + 1)) j : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ioc_subset_Ioc_left (Nat.zero_le _))
            (fun _ _ _ => Nat.cast_nonneg _)
  have hE0 : (0 : ℝ) < ramificationIndex K (charTower η (k + 1)) := by
    exact_mod_cast ramificationIndex_pos K (charTower η (k + 1))
  rw [le_div_iff₀ hE0]
  refine le_trans (le_of_eq ?_) hψlow
  rw [hE]
  push_cast
  have hsum : ∑ i ∈ Finset.range (k - artinLevel K η n₀), (p : ℝ) ^ ((k : ℤ) - i) =
      (p : ℝ) ^ (k : ℤ) * ∑ i ∈ Finset.range (k - artinLevel K η n₀), (p : ℝ) ^ (-(i : ℤ)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← zpow_add₀ hp0.ne']
    ring_nf
  rw [hsum, ← zpow_natCast (p : ℝ) (k + 1 - artinLevel K η n'), Nat.cast_sub (by omega),
    zpow_sub₀ hp0.ne', zpow_neg]
  push_cast
  rw [zpow_add₀ hp0.ne', zpow_one]
  field_simp

theorem nrm_sub_le_of_mem_unitsOneAdd (hη : Continuous η) (hA : ∀ n, artinImage K η n ≠ ⊥)
    {n' n₀ e : ℕ} (hn' : n' ≤ n₀) (h2 : 2 ≤ artinLevel K η n')
    (hper : ∀ n, n₀ ≤ n → artinLevel K η (n + e) = artinLevel K η n + 1)
    {k : ℕ} (hk : artinLevel K η n₀ ≤ k) {σ : Gal(PadicAlgCl p/K)} (hσ : η σ ∈ unitsOneAdd p k)
    {y : PadicAlgCl p} (hy : y ∈ charTower η (k + 1)) :
    nrm K (σ y - y) ≤ baseUnifNrm K (PadicAlgCl p) ^ ((e : ℝ) / p *
      ∑ i ∈ Finset.range (k - artinLevel K η n₀), (p : ℝ) ^ (-(i : ℤ))) * nrm K y := by
  have : FiniteDimensional K (charTower η (k + 1)) := finiteDimensional_charTower hη (k + 1)
  have : IsAbelianGalois K (charTower η (k + 1)) := isAbelianGalois_charTower hη (k + 1)
  have hmono := artinLevel_mono hA
  obtain ⟨N, hNk, hN1, hNq⟩ := exists_last_artinLevel_le hA hper hk
  have hn'N : n' ≤ N := le_trans hn' (le_trans (Nat.le_add_right _ _) hNq)
  have h2N : 2 ≤ artinLevel K η N := h2.trans (hmono hn'N)
  have hσN : AlgEquiv.restrictNormalHom (charTower η (k + 1)) σ ∈
      upperRamificationGroup K (charTower η (k + 1)) N := by
    rw [restrictNormalHom_mem_upperRamificationGroup_iff_level hη (hA N) h2N,
      min_eq_left (by omega)]
    exact unitsOneAdd_antitone hNk hσ
  have hψ0 : 0 ≤ herbrandPsi K (charTower η (k + 1)) N := by
    rw [← herbrandPsi_zero (K := K) (L := charTower η (k + 1))]
    exact herbrandPsi_strictMono.monotone (Nat.cast_nonneg N)
  obtain ⟨i, hi⟩ : ∃ i : ℕ, (i : ℤ) = ⌈herbrandPsi K (charTower η (k + 1)) N⌉ :=
    ⟨_, Int.toNat_of_nonneg (Int.ceil_nonneg hψ0)⟩
  have hmem : AlgEquiv.restrictNormalHom (charTower η (k + 1)) σ ∈
      lowerRamificationGroup K (charTower η (k + 1)) (i : ℤ) := by
    rw [hi]
    exact hσN
  have h1 := nrm_sub_le_of_mem_lowerRamificationGroup (charTower η (k + 1)) hmem ⟨y, hy⟩
  refine h1.trans (mul_le_mul_of_nonneg_right ?_ (nrm_nonneg _))
  have hX := le_herbrandPsi_div_ramificationIndex hη hA hn' h2 hper hNk hN1 hNq
  have hu0 : 0 < unifNrm (charTower η (k + 1)) := unifNrm_pos _
  have hu1 : unifNrm (charTower η (k + 1)) < 1 := unifNrm_lt_one _
  have huE : unifNrm (charTower η (k + 1)) ^ ramificationIndex K (charTower η (k + 1)) =
      baseUnifNrm K (PadicAlgCl p) := unifNrm_pow_ramificationIndex _
  have hE0 : (0 : ℝ) < ramificationIndex K (charTower η (k + 1)) := by
    exact_mod_cast ramificationIndex_pos K (charTower η (k + 1))
  calc unifNrm (charTower η (k + 1)) ^ i = unifNrm (charTower η (k + 1)) ^ (i : ℝ) :=
        (Real.rpow_natCast _ i).symm
    _ ≤ unifNrm (charTower η (k + 1)) ^ herbrandPsi K (charTower η (k + 1)) N := by
        refine Real.rpow_le_rpow_of_exponent_ge hu0 hu1.le ?_
        have : ((⌈herbrandPsi K (charTower η (k + 1)) N⌉ : ℤ) : ℝ) = (i : ℝ) := by
          rw [← hi]; norm_cast
        rw [← this]
        exact Int.le_ceil _
    _ = baseUnifNrm K (PadicAlgCl p) ^
          (herbrandPsi K (charTower η (k + 1)) N / ramificationIndex K (charTower η (k + 1))) := by
        rw [← huE, ← Real.rpow_natCast, ← Real.rpow_mul hu0.le]
        congr 1
        field_simp
    _ ≤ baseUnifNrm K (PadicAlgCl p) ^ ((e : ℝ) / p *
          ∑ i ∈ Finset.range (k - artinLevel K η n₀), (p : ℝ) ^ (-(i : ℤ))) :=
        Real.rpow_le_rpow_of_exponent_ge baseUnifNrm_pos
          (by rw [← huE]; exact pow_le_one₀ hu0.le hu1.le) hX

end SenTateChar

end GroundTheory.PAdicHodge
