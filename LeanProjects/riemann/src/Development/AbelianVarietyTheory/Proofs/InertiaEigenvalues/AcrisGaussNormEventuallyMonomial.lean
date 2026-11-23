import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Acris0TorsionFree
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

open Filter Topology

namespace GlobalTheory.GaussSlope

theorem eventually_iSup_eq_monomial (c : ℕ → ℝ) (h0 : ∀ n, 0 ≤ c n) (h1 : ∀ n, c n ≤ 1) {ρ : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (hG : (⨆ n, c n * ρ ^ n) ≠ 0) :
    ∃ i, ∀ᶠ r in 𝓝[≥] ρ, (⨆ n, c n * r ^ n) = c i * r ^ i := by
  obtain ⟨j, hj⟩ : ∃ j, 0 < c j := by
    by_contra h
    push Not at h
    apply hG
    have : ∀ n, c n = 0 := fun n => le_antisymm (h n) (h0 n)
    simp [this]
  obtain ⟨σ, hσ, hσ1⟩ := exists_between hρ1
  have hσ0 : 0 < σ := hρ.trans hσ
  obtain ⟨M, hM⟩ := exists_pow_lt_of_lt_one (mul_pos hj (pow_pos hρ j)) hσ1
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image (insert j (Finset.range M))
    (fun n => toLex (c n * ρ ^ n, n)) ⟨j, Finset.mem_insert_self _ _⟩
  have key : ∀ n ∈ insert j (Finset.range M), ∀ᶠ r in 𝓝[≥] ρ, c n * r ^ n ≤ c i * r ^ i := by
    intro n hn
    rcases Prod.Lex.toLex_le_toLex.1 (hi n hn) with h | ⟨h, h'⟩
    · have : ∀ᶠ r in 𝓝 ρ, c n * r ^ n < c i * r ^ i :=
        ContinuousAt.eventually_lt (f := fun r : ℝ => c n * r ^ n) (g := fun r : ℝ => c i * r ^ i)
          (by fun_prop) (by fun_prop) h
      exact (this.filter_mono nhdsWithin_le_nhds).mono fun _ h => h.le
    · filter_upwards [self_mem_nhdsWithin] with r hr
      have hr : ρ ≤ r := hr
      simp only at h h'
      have e : ∀ m, c m * r ^ m = c m * ρ ^ m * (r / ρ) ^ m := fun m => by
        rw [div_pow]; field_simp
      rw [e n, e i, h]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ((one_le_div hρ).2 hr) h')
        (mul_nonneg (h0 _) (pow_nonneg hρ.le _))
  refine ⟨i, ?_⟩
  have hlt : ∀ᶠ r in 𝓝[≥] ρ, r < σ := (gt_mem_nhds hσ).filter_mono nhdsWithin_le_nhds
  filter_upwards [(eventually_all_finset _).2 key, hlt, self_mem_nhdsWithin] with r hk hrσ hr
  have hr : ρ ≤ r := hr
  have hr0 : 0 ≤ r := hρ.le.trans hr
  have hall : ∀ n, c n * r ^ n ≤ c i * r ^ i := by
    intro n
    by_cases hn : n < M
    · exact hk n (Finset.mem_insert_of_mem (Finset.mem_range.2 hn))
    · refine le_trans ?_ (hk j (Finset.mem_insert_self _ _))
      calc c n * r ^ n ≤ 1 * σ ^ n := by gcongr; exact h1 n
        _ ≤ σ ^ M := by rw [one_mul]; exact pow_le_pow_of_le_one hσ0.le hσ1.le (not_lt.1 hn)
        _ ≤ c j * ρ ^ j := hM.le
        _ ≤ c j * r ^ j := by gcongr
  exact le_antisymm (ciSup_le hall) (le_ciSup (f := fun n => c n * r ^ n) ⟨_, Set.forall_mem_range.2 hall⟩ i)

theorem add_eq_of_lt {R : Type} [CommRing R] (N : R → ℝ) (hadd : ∀ x y, N (x + y) ≤ max (N x) (N y))
    (hneg : ∀ x, N (-x) = N x) {x y : R} (h : N y < N x) : N (x + y) = N x := by
  refine le_antisymm ((hadd x y).trans (max_le le_rfl h.le)) ?_
  have := hadd (x + y) (-y)
  rw [add_neg_cancel_right, hneg] at this
  rcases le_max_iff.1 this with h' | h'
  · exact h'
  · exact absurd h' (not_le.2 h)

theorem map_pow_mul {R : Type} [CommRing R] (N : R → ℝ) (hmul : ∀ x y, N (x * y) = N x * N y)
    (p x : R) (k : ℕ) : N (p ^ k * x) = N p ^ k * N x := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', mul_assoc, hmul, ih]; ring

theorem slope_abstract {R : Type} [CommRing R] (p : R) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1) (N : ℝ → R → ℝ)
    (hN : ∀ r, ρ ≤ r → r < 1 → (∀ x, N r x ≤ 1) ∧ (∀ x y, N r (x + y) ≤ max (N r x) (N r y)) ∧
      (∀ x, N r (-x) = N r x) ∧ (∀ x y, N r (x * y) = N r x * N r y) ∧ N r p = r)
    (b : R) (hb : 0 < N ρ b)
    (hd : ∀ n : ℕ, ∃ (k : ℕ) (a z : R) (c : ℕ → ℝ), p ^ k * b = a + p ^ (k + n) * z ∧ (∀ n, 0 ≤ c n) ∧
      (∀ n, c n ≤ 1) ∧ ∀ r, ρ ≤ r → r < 1 → N r a = ⨆ n, c n * r ^ n) :
    ∃ (r₁ c : ℝ) (k : ℤ), ρ < r₁ ∧ r₁ < 1 ∧ 0 < c ∧ ∀ r, ρ < r → r < r₁ → N r b = c * r ^ k := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hb hρ1
  obtain ⟨k, a, z, c, hab, h0, h1, hc⟩ := hd n
  have hz : ∀ r, ρ ≤ r → r < 1 → N r (p ^ (k + n) * z) ≤ r ^ (k + n) := by
    intro r hr hr1
    obtain ⟨e1, -, -, e4, e5⟩ := hN r hr hr1
    rw [map_pow_mul _ e4, e5]
    exact mul_le_of_le_one_right (pow_nonneg (hρ.le.trans hr) _) (e1 z)
  have hbb : ∀ r, ρ ≤ r → r < 1 → N r (p ^ k * b) = r ^ k * N r b := by
    intro r hr hr1
    obtain ⟨e1, -, -, e4, e5⟩ := hN r hr hr1
    rw [map_pow_mul _ e4, e5]
  have ha : ρ ^ (k + n) < N ρ a := by
    obtain ⟨e1, e2, e3, e4, e5⟩ := hN ρ le_rfl hρ1
    have h2 : ρ ^ (k + n) < N ρ (p ^ k * b) := by
      rw [hbb ρ le_rfl hρ1, pow_add]
      exact mul_lt_mul_of_pos_left hn (pow_pos hρ _)
    have h3 : a = p ^ k * b + -(p ^ (k + n) * z) := by rw [hab]; ring
    rw [h3, add_eq_of_lt _ e2 e3 (by rw [e3]; exact (hz ρ le_rfl hρ1).trans_lt h2)]
    exact h2
  rw [hc ρ le_rfl hρ1] at ha
  obtain ⟨i, hi⟩ := eventually_iSup_eq_monomial c h0 h1 hρ hρ1 ((pow_pos hρ _).trans ha).ne'
  rw [hi.self_of_nhdsWithin Set.self_mem_Ici] at ha
  have hci : 0 < c i := (mul_pos_iff_of_pos_right (pow_pos hρ i)).1 ((pow_pos hρ _).trans ha)
  have h4 : ∀ᶠ r in 𝓝 ρ, r ^ (k + n) < c i * r ^ i :=
    ContinuousAt.eventually_lt (f := fun r : ℝ => r ^ (k + n)) (g := fun r : ℝ => c i * r ^ i)
      (by fun_prop) (by fun_prop) ha
  have h5 : ∀ᶠ r in 𝓝[≥] ρ, r < 1 → N r b = c i * r ^ ((i : ℤ) - k) := by
    filter_upwards [hi, h4.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with r hr1 hr2 hr hr3
    have hr : ρ ≤ r := hr
    have hr0 : 0 < r := hρ.trans_le hr
    obtain ⟨e1, e2, e3, e4, e5⟩ := hN r hr hr3
    have h6 := hbb r hr hr3
    have h7 : N r a = c i * r ^ i := by rw [hc r hr hr3, hr1]
    rw [hab, add_eq_of_lt _ e2 e3 (by rw [h7]; exact (hz r hr hr3).trans_lt hr2), h7] at h6
    rw [zpow_sub₀ hr0.ne', zpow_natCast, zpow_natCast, ← mul_div_assoc, h6]
    field_simp
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.1 h5
  obtain ⟨σ, hσ, hσ1⟩ := exists_between hρ1
  refine ⟨min u σ, c i, (i : ℤ) - k, lt_min hu hσ, (min_le_right _ _).trans_lt hσ1, hci, fun r hr hr' => ?_⟩
  exact hsub ⟨hr.le, hr'.trans_le (min_le_left _ _)⟩ ((hr'.trans_le (min_le_right _ _)).trans hσ1)

variable (l : ℕ) [Fact l.Prime]

theorem untilt_zero : (0 : Per.Fl l).untilt = 0 :=
  Perfection.teichmuller_zero

theorem exists_pow_mul_eq (s : Per.Acris0 l) : ∃ (k : ℕ) (a : Per.Ainf l),
    (l : Per.Acris l) ^ k * algebraMap (Per.Acris0 l) (Per.Acris l) s = algebraMap (Per.Ainf l) (Per.Acris l) a := by
  obtain ⟨k, a, h⟩ := IsLocalization.Away.surj (l : Per.Ainf l) (s : Per.AinfP l)
  refine ⟨k, a, ?_⟩
  have h1 : (l : Per.Acris0 l) ^ k * s = algebraMap (Per.Ainf l) (Per.Acris0 l) a := by
    apply Subtype.ext
    rw [map_natCast, mul_comm] at h
    simpa using h
  have h2 : algebraMap (Per.Ainf l) (Per.Acris l) a =
      algebraMap (Per.Acris0 l) (Per.Acris l) (algebraMap (Per.Ainf l) (Per.Acris0 l) a) :=
    GlobalTheory.RingIface.tower (l := l) a
  rw [h2, ← h1, map_mul, map_pow, map_natCast]

theorem gauss_l {r : ℝ} (hr : 0 ≤ r) :
    (⨆ n : ℕ, ‖((((l : Per.Ainf l).coeff n).untilt : Per.OC l) : ℂ_[l])‖ ^ ((1 : ℝ) / (l : ℝ) ^ n) * r ^ n) = r := by
  have hl : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  have h : ∀ n : ℕ, ‖((((l : Per.Ainf l).coeff n).untilt : Per.OC l) : ℂ_[l])‖ ^ ((1 : ℝ) / (l : ℝ) ^ n) * r ^ n
      = if n = 1 then r else 0 := by
    intro n
    rw [WittVector.coeff_p]
    split_ifs with h
    · subst h
      simp
    · rw [untilt_zero]
      have : (1 : ℝ) / (l : ℝ) ^ n ≠ 0 := by positivity
      simp only [ZeroMemClass.coe_zero, norm_zero, Real.zero_rpow this, zero_mul]
  simp only [h]
  have hall : ∀ n : ℕ, (if n = 1 then r else 0) ≤ r := fun n => by split_ifs <;> simp [hr]
  exact le_antisymm (ciSup_le hall)
    (le_ciSup_of_le (f := fun n : ℕ => if n = 1 then r else 0) ⟨_, Set.forall_mem_range.2 hall⟩ 1 (by simp))

end GlobalTheory.GaussSlope

namespace GlobalTheory.MemLoc
open GlobalTheory.GaussSlope

theorem gauss_slope : ∀ (l : ℕ) [Fact l.Prime] (N : ℝ → Per.Acris l → ℝ), (∀ r : ℝ, (l : ℝ)⁻¹ ≤ r → r < 1 → (∀ x, 0 ≤ N r x ∧ N r x ≤ 1) ∧ (∀ x y, N r (x + y) ≤ max (N r x) (N r y)) ∧ (∀ x, N r (-x) = N r x) ∧ (∀ x y, N r (x * y) = N r x * N r y) ∧ ∀ a : Per.Ainf l, N r (algebraMap (Per.Ainf l) (Per.Acris l) a) = ⨆ n : ℕ, ‖(((a.coeff n).untilt : Per.OC l) : ℂ_[l])‖ ^ ((1 : ℝ) / (l : ℝ) ^ n) * r ^ n) → ∀ b : Per.Acris l, N (l : ℝ)⁻¹ b ≠ 0 → ∃ (r₁ c : ℝ) (k : ℤ), (l : ℝ)⁻¹ < r₁ ∧ r₁ < 1 ∧ 0 < c ∧ ∀ r, (l : ℝ)⁻¹ < r → r < r₁ → N r b = c * r ^ k := by
  intro l _ N hN b hb
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hρ : (0 : ℝ) < (l : ℝ)⁻¹ := by positivity
  have hρ1 : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl
  refine slope_abstract (l : Per.Acris l) hρ hρ1 N (fun r hr hr1 => ?_) b
    (lt_of_le_of_ne ((hN _ le_rfl hρ1).1 b).1 hb.symm) fun n => ?_
  · obtain ⟨e1, e2, e3, e4, e5⟩ := hN r hr hr1
    refine ⟨fun x => (e1 x).2, e2, e3, e4, ?_⟩
    rw [← map_natCast (algebraMap (Per.Ainf l) (Per.Acris l)) l, e5, gauss_l l (hρ.le.trans hr)]
  · obtain ⟨s, z, h⟩ := (acris_basic l).2.2.1 b n
    obtain ⟨k, a, ha⟩ := exists_pow_mul_eq l s
    refine ⟨k, _, z, fun n => ‖(((a.coeff n).untilt : Per.OC l) : ℂ_[l])‖ ^ ((1 : ℝ) / (l : ℝ) ^ n), ?_,
      fun n => by positivity, fun n => ?_, fun r hr hr1 => (hN r hr hr1).2.2.2.2 a⟩
    · rw [h, mul_add, ha, pow_add, mul_assoc]
    · exact Real.rpow_le_one (norm_nonneg _) ((GlobalTheory.RingBasics.mem_OC _).1 (Subtype.prop _)) (by positivity)

end GlobalTheory.MemLoc
