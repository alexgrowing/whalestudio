import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsGauss
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsGaussGCTarget
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaussNormAcrisRadiusPosDefiniteStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisGaussNormEventuallyMonomial
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Acris0TorsionFree
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics

noncomputable section

open Filter Topology
open GlobalTheory.PMon.Gauss
open scoped Formalism.Per

namespace GlobalTheory.GaussMono

theorem eventually_iSup_eq_monomial_left (c : ℕ → ℝ) (h0 : ∀ n, 0 ≤ c n) (h1 : ∀ n, c n ≤ 1) {ρ : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (hG : (⨆ n, c n * ρ ^ n) ≠ 0) :
    ∃ i, ∀ᶠ r in 𝓝[≤] ρ, (⨆ n, c n * r ^ n) = c i * r ^ i := by
  obtain ⟨j, hj⟩ : ∃ j, 0 < c j := by
    by_contra h
    push_neg at h
    apply hG
    have : ∀ n, c n = 0 := fun n => le_antisymm (h n) (h0 n)
    simp [this]
  have hσ0 : 0 < ρ / 2 := by positivity
  have hσρ : ρ / 2 < ρ := by linarith
  obtain ⟨M, hM⟩ := exists_pow_lt_of_lt_one (mul_pos hj (pow_pos hσ0 j)) hρ1
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image (insert j (Finset.range M))
    (fun n => toLex (c n * ρ ^ n, OrderDual.toDual n)) ⟨j, Finset.mem_insert_self _ _⟩
  have hpos : ∀ᶠ r in 𝓝[≤] ρ, ρ / 2 < r := (eventually_gt_nhds hσρ).filter_mono nhdsWithin_le_nhds
  have key : ∀ n ∈ insert j (Finset.range M), ∀ᶠ r in 𝓝[≤] ρ, c n * r ^ n ≤ c i * r ^ i := by
    intro n hn
    rcases Prod.Lex.toLex_le_toLex.1 (hi n hn) with h | ⟨h, h'⟩
    · have : ∀ᶠ r in 𝓝 ρ, c n * r ^ n < c i * r ^ i :=
        ContinuousAt.eventually_lt (f := fun r : ℝ => c n * r ^ n) (g := fun r : ℝ => c i * r ^ i)
          (by fun_prop) (by fun_prop) h
      exact (this.filter_mono nhdsWithin_le_nhds).mono fun _ h => h.le
    · filter_upwards [self_mem_nhdsWithin, hpos] with r hr hr0
      have hr : r ≤ ρ := hr
      have hr0 : 0 ≤ r := hσ0.le.trans hr0.le
      simp only at h h'
      have hin : i ≤ n := OrderDual.toDual_le_toDual.1 h'
      have e : ∀ m, c m * r ^ m = c m * ρ ^ m * (r / ρ) ^ m := fun m => by
        rw [div_pow]; field_simp
      rw [e n, e i, h]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_of_le_one (div_nonneg hr0 hρ.le) ((div_le_one hρ).2 hr) hin)
        (mul_nonneg (h0 _) (pow_nonneg hρ.le _))
  refine ⟨i, ?_⟩
  filter_upwards [(eventually_all_finset _).2 key, hpos, self_mem_nhdsWithin] with r hk hrσ hr
  have hr : r ≤ ρ := hr
  have hr0 : 0 ≤ r := hσ0.le.trans hrσ.le
  have hall : ∀ n, c n * r ^ n ≤ c i * r ^ i := by
    intro n
    by_cases hn : n < M
    · exact hk n (Finset.mem_insert_of_mem (Finset.mem_range.2 hn))
    · refine le_trans ?_ (hk j (Finset.mem_insert_self _ _))
      calc c n * r ^ n ≤ 1 * ρ ^ n := by gcongr; exact h1 n
        _ ≤ ρ ^ M := by rw [one_mul]; exact pow_le_pow_of_le_one hρ.le hρ1.le (not_lt.1 hn)
        _ ≤ c j * (ρ / 2) ^ j := hM.le
        _ ≤ c j * r ^ j := by gcongr
  exact le_antisymm (ciSup_le hall) (le_ciSup (f := fun n => c n * r ^ n) ⟨_, Set.forall_mem_range.2 hall⟩ i)

theorem eventually_monomial {R : Type} [CommRing R] (p : R) {L ρ : ℝ} (hL : 0 < L) (hLρ : L ≤ ρ) (hρ1 : ρ < 1)
    (N : ℝ → R → ℝ)
    (hN : ∀ r, L ≤ r → r < 1 → (∀ x, N r x ≤ 1) ∧ (∀ x y, N r (x + y) ≤ max (N r x) (N r y)) ∧
      (∀ x, N r (-x) = N r x) ∧ (∀ x y, N r (x * y) = N r x * N r y) ∧ N r p = r)
    (b : R) (hb : 0 < N ρ b)
    (hd : ∀ n : ℕ, ∃ (k : ℕ) (a z : R) (c : ℕ → ℝ), p ^ k * b = a + p ^ (k + n) * z ∧ (∀ n, 0 ≤ c n) ∧
      (∀ n, c n ≤ 1) ∧ ∀ r, L ≤ r → r < 1 → N r a = ⨆ n, c n * r ^ n)
    (f : Filter ℝ) (hf : f ≤ 𝓝 ρ) (hf0 : pure ρ ≤ f) (hfL : ∀ᶠ r in f, L ≤ r ∧ r < 1)
    (hmono : ∀ c : ℕ → ℝ, (∀ n, 0 ≤ c n) → (∀ n, c n ≤ 1) → (⨆ n, c n * ρ ^ n) ≠ 0 →
      ∃ i, ∀ᶠ r in f, (⨆ n, c n * r ^ n) = c i * r ^ i) :
    ∃ (c : ℝ) (k : ℤ), 0 < c ∧ ∀ᶠ r in f, N r b = c * r ^ k := by
  have hρ : 0 < ρ := hL.trans_le hLρ
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hb hρ1
  obtain ⟨k, a, z, c, hab, h0, h1, hc⟩ := hd n
  have hz : ∀ r, L ≤ r → r < 1 → N r (p ^ (k + n) * z) ≤ r ^ (k + n) := by
    intro r hr hr1
    obtain ⟨e1, -, -, e4, e5⟩ := hN r hr hr1
    rw [GlobalTheory.GaussSlope.map_pow_mul _ e4, e5]
    exact mul_le_of_le_one_right (pow_nonneg (hL.le.trans hr) _) (e1 z)
  have hbb : ∀ r, L ≤ r → r < 1 → N r (p ^ k * b) = r ^ k * N r b := by
    intro r hr hr1
    obtain ⟨-, -, -, e4, e5⟩ := hN r hr hr1
    rw [GlobalTheory.GaussSlope.map_pow_mul _ e4, e5]
  have ha : ρ ^ (k + n) < N ρ a := by
    obtain ⟨-, e2, e3, -, -⟩ := hN ρ hLρ hρ1
    have h2 : ρ ^ (k + n) < N ρ (p ^ k * b) := by
      rw [hbb ρ hLρ hρ1, pow_add]
      exact mul_lt_mul_of_pos_left hn (pow_pos hρ _)
    have h3 : a = p ^ k * b + -(p ^ (k + n) * z) := by rw [hab]; ring
    rw [h3, GlobalTheory.GaussSlope.add_eq_of_lt _ e2 e3 (by rw [e3]; exact (hz ρ hLρ hρ1).trans_lt h2)]
    exact h2
  rw [hc ρ hLρ hρ1] at ha
  obtain ⟨i, hi⟩ := hmono c h0 h1 ((pow_pos hρ _).trans ha).ne'
  have hiρ : (⨆ n, c n * ρ ^ n) = c i * ρ ^ i := Filter.mem_pure.1 (hf0 hi)
  rw [hiρ] at ha
  have hci : 0 < c i := (mul_pos_iff_of_pos_right (pow_pos hρ i)).1 ((pow_pos hρ _).trans ha)
  have h4 : ∀ᶠ r in 𝓝 ρ, r ^ (k + n) < c i * r ^ i :=
    ContinuousAt.eventually_lt (f := fun r : ℝ => r ^ (k + n)) (g := fun r : ℝ => c i * r ^ i)
      (by fun_prop) (by fun_prop) ha
  refine ⟨c i, (i : ℤ) - k, hci, ?_⟩
  filter_upwards [hi, hf h4, hfL] with r hr1 hr2 hr
  obtain ⟨hr, hr3⟩ := hr
  have hr0 : 0 < r := hL.trans_le hr
  obtain ⟨-, e2, e3, -, -⟩ := hN r hr hr3
  have h6 := hbb r hr hr3
  have h7 : N r a = c i * r ^ i := by rw [hc r hr hr3, hr1]
  rw [hab, GlobalTheory.GaussSlope.add_eq_of_lt _ e2 e3 (by rw [h7]; exact (hz r hr hr3).trans_lt hr2), h7] at h6
  rw [zpow_sub₀ hr0.ne', zpow_natCast, zpow_natCast, ← mul_div_assoc, h6]
  field_simp

end GlobalTheory.GaussMono

namespace GlobalTheory.PMon.Gauss

theorem gC_monomial_near : ∀ (l : ℕ) [Fact l.Prime] (x : Formalism.Per.Acris l), x ≠ 0 → ∀ ρ₀ : ℝ, (l : ℝ)⁻¹ ≤ ρ₀ →
    ρ₀ < 1 → (∃ (c : ℝ) (k : ℤ) (ρ₂ : ℝ), 0 < c ∧ ρ₀ < ρ₂ ∧ ρ₂ < 1 ∧
      ∀ ρ ∈ Set.Icc ρ₀ ρ₂, gC l ρ x = c * ρ ^ k) ∧
    ((l : ℝ)⁻¹ < ρ₀ → ∃ (c : ℝ) (k : ℤ) (ρ₁ : ℝ), 0 < c ∧ (l : ℝ)⁻¹ ≤ ρ₁ ∧ ρ₁ < ρ₀ ∧
      ∀ ρ ∈ Set.Icc ρ₁ ρ₀, gC l ρ x = c * ρ ^ k) := by
  intro l _ x hx ρ₀ hρl hρ1
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hL : (0 : ℝ) < (l : ℝ)⁻¹ := by positivity
  have hρ0 : 0 < ρ₀ := hL.trans_le hρl
  have hN : ∀ r, (l : ℝ)⁻¹ ≤ r → r < 1 → (∀ y, gC l r y ≤ 1) ∧
      (∀ y z, gC l r (y + z) ≤ max (gC l r y) (gC l r z)) ∧ (∀ y, gC l r (-y) = gC l r y) ∧
      (∀ y z, gC l r (y * z) = gC l r y * gC l r z) ∧ gC l r (l : Formalism.Per.Acris l) = r := by
    intro r hr hr1
    obtain ⟨e1, e2, e3, e4, e5⟩ := isGauss_gC_target l r hr hr1
    refine ⟨fun y => (e1 y).2, e2, e3, e4, ?_⟩
    rw [← map_natCast (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l)) l, e5]
    exact GlobalTheory.GaussSlope.gauss_l l (hL.le.trans hr)
  have hd : ∀ n : ℕ, ∃ (k : ℕ) (a z : Formalism.Per.Acris l) (c : ℕ → ℝ),
      (l : Formalism.Per.Acris l) ^ k * x = a + (l : Formalism.Per.Acris l) ^ (k + n) * z ∧ (∀ n, 0 ≤ c n) ∧
      (∀ n, c n ≤ 1) ∧ ∀ r, (l : ℝ)⁻¹ ≤ r → r < 1 → gC l r a = ⨆ n, c n * r ^ n := by
    intro n
    obtain ⟨s, z, h⟩ := (GlobalTheory.MemLoc.acris_basic l).2.2.1 x n
    obtain ⟨k, a, ha⟩ := GlobalTheory.GaussSlope.exists_pow_mul_eq l s
    refine ⟨k, algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l) a, z,
      fun n => ‖(((a.coeff n).untilt : Formalism.Per.OC l) : ℂ_[l])‖ ^ ((1 : ℝ) / (l : ℝ) ^ n), ?_,
      fun n => by positivity, fun n => ?_, fun r hr hr1 => (isGauss_gC_target l r hr hr1).2.2.2.2 a⟩
    · rw [h, mul_add, ha, pow_add, mul_assoc]
    · exact Real.rpow_le_one (norm_nonneg _) ((GlobalTheory.RingBasics.mem_OC _).1 (Subtype.prop _)) (by positivity)
  have hb : 0 < gC l ρ₀ x := GlobalTheory.T.gaussNormAcrisRadius_pos_definite l x hx ρ₀ hρl hρ1
  constructor
  · have hfL : ∀ᶠ r in 𝓝[≥] ρ₀, (l : ℝ)⁻¹ ≤ r ∧ r < 1 := by
      filter_upwards [self_mem_nhdsWithin, (eventually_lt_nhds hρ1).filter_mono nhdsWithin_le_nhds] with r hr hr1
      exact ⟨hρl.trans hr, hr1⟩
    obtain ⟨c, k, hc, hev⟩ := GlobalTheory.GaussMono.eventually_monomial (l : Formalism.Per.Acris l) hL hρl hρ1 (gC l) hN x hb
      hd (𝓝[≥] ρ₀) nhdsWithin_le_nhds (pure_le_nhdsWithin (Set.mem_Ici.2 le_rfl)) hfL
      (fun c h0 h1 hG => GlobalTheory.GaussSlope.eventually_iSup_eq_monomial c h0 h1 hρ0 hρ1 hG)
    obtain ⟨u, hu, hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.1 hev
    have hu : ρ₀ < u := hu
    obtain ⟨ρ₂, h2a, h2b⟩ := exists_between (lt_min hu hρ1)
    exact ⟨c, k, ρ₂, hc, h2a, h2b.trans_le (min_le_right _ _),
      fun r hr => hsub ⟨hr.1, hr.2.trans_lt (h2b.trans_le (min_le_left _ _))⟩⟩
  · intro hlt
    have hfL : ∀ᶠ r in 𝓝[≤] ρ₀, (l : ℝ)⁻¹ ≤ r ∧ r < 1 := by
      filter_upwards [self_mem_nhdsWithin, (eventually_gt_nhds hlt).filter_mono nhdsWithin_le_nhds] with r hr hr1
      exact ⟨(hr1 : (l : ℝ)⁻¹ < r).le, (hr : r ≤ ρ₀).trans_lt hρ1⟩
    obtain ⟨c, k, hc, hev⟩ := GlobalTheory.GaussMono.eventually_monomial (l : Formalism.Per.Acris l) hL hρl hρ1 (gC l) hN x hb
      hd (𝓝[≤] ρ₀) nhdsWithin_le_nhds (pure_le_nhdsWithin (Set.mem_Iic.2 le_rfl)) hfL
      (fun c h0 h1 hG => GlobalTheory.GaussMono.eventually_iSup_eq_monomial_left c h0 h1 hρ0 hρ1 hG)
    obtain ⟨u, hu, hsub⟩ := mem_nhdsLE_iff_exists_Ioc_subset.1 hev
    have hu : u < ρ₀ := hu
    obtain ⟨ρ₁, h1a, h1b⟩ := exists_between (max_lt hu hlt)
    exact ⟨c, k, ρ₁, hc, (le_max_right _ _).trans h1a.le, h1b,
      fun r hr => hsub ⟨(le_max_left _ _).trans_lt (h1a.trans_le hr.1), hr.2⟩⟩

end GlobalTheory.PMon.Gauss

end
