import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EncardSeminormBallMulLeConvexityStatement
open Filter Topology GlobalTheory.VolBr

namespace GlobalTheory.VolBr

theorem IsBallFam.subset_of_le_radius {G : Type} [AddCommGroup G] {Λ : AddSubgroup G} {B : ℝ → Set G}
    (h : IsBallFam Λ B) {r r' : ℝ} (hr : r ≤ r') : B r ⊆ B r' := by
  intro x hx
  have := h.sub_mem r (r' - r) x 0 hx (h.zero_mem _ (by linarith))
  simpa using this

theorem IsBallFam.ncard_sq_le_of_ceil {G : Type} [AddCommGroup G] {Λ : AddSubgroup G} {B : ℝ → Set G}
    (h : IsBallFam Λ B) (hfin : ∀ R, (B R).Finite) {e E : ℝ} (he : 1 ≤ e)
    (hE : (⌈2 * e⌉₊ : ℝ) ^ 2 + (⌈2 * e⌉₊ : ℝ) / 2 ≤ E) :
    ((B e).ncard : ℝ) ^ 2 ≤ (B 1).ncard * (B E).ncard := by
  have hn2 : 2 * e ≤ (⌈2 * e⌉₊ : ℝ) := Nat.le_ceil _
  have hnpos : 0 < ⌈2 * e⌉₊ := by
    have : (0:ℝ) < (⌈2 * e⌉₊ : ℝ) := by linarith
    exact_mod_cast this
  have key := GlobalTheory.T.encard_seminormBall_mul_le_convexity G Λ B h _ hnpos (hfin _)
  rw [← (hfin _).cast_ncard_eq, ← (hfin _).cast_ncard_eq, ← (hfin _).cast_ncard_eq,
    ← (hfin _).cast_ncard_eq] at key
  have key' : (B (⌈2 * e⌉₊ : ℝ)).ncard * (B ((⌈2 * e⌉₊ : ℝ) / 2)).ncard ≤
      (B 1).ncard * (B ((⌈2 * e⌉₊ : ℝ) ^ 2 + (⌈2 * e⌉₊ : ℝ) / 2)).ncard := by
    have := key
    exact_mod_cast this
  have h1 : (B e).ncard ≤ (B (⌈2 * e⌉₊ : ℝ)).ncard :=
    Set.ncard_le_ncard (h.subset_of_le_radius (by linarith)) (hfin _)
  have h2 : (B e).ncard ≤ (B ((⌈2 * e⌉₊ : ℝ) / 2)).ncard :=
    Set.ncard_le_ncard (h.subset_of_le_radius (by linarith)) (hfin _)
  have h3 : (B ((⌈2 * e⌉₊ : ℝ) ^ 2 + (⌈2 * e⌉₊ : ℝ) / 2)).ncard ≤ (B E).ncard :=
    Set.ncard_le_ncard (h.subset_of_le_radius hE) (hfin _)
  have : (B e).ncard ^ 2 ≤ (B 1).ncard * (B E).ncard := by
    calc (B e).ncard ^ 2 = (B e).ncard * (B e).ncard := sq _
      _ ≤ (B (⌈2 * e⌉₊ : ℝ)).ncard * (B ((⌈2 * e⌉₊ : ℝ) / 2)).ncard := Nat.mul_le_mul h1 h2
      _ ≤ (B 1).ncard * (B ((⌈2 * e⌉₊ : ℝ) ^ 2 + (⌈2 * e⌉₊ : ℝ) / 2)).ncard := key'
      _ ≤ _ := Nat.mul_le_mul_left _ h3
  exact_mod_cast this

theorem log_ncard_ball_one_eventually_ge : ∀ (G : Type) [AddCommGroup G] (Λ : ℕ → AddSubgroup G)
    (B : ℕ → ℝ → Set G) (d : ℕ), 0 < d → (∀ m, IsBallFam (Λ m) (B m)) → (∀ m R, (B m R).Finite) →
    ∀ α β t₀ : ℝ, (∀ t, t₀ ≤ t → Tendsto (fun m : ℕ => Real.log ((B m (Real.exp (t * m))).ncard : ℝ) /
      (m : ℝ) ^ d) atTop (𝓝 (α + β * t))) → ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop,
      (α - ε) * (m : ℝ) ^ d ≤ Real.log ((B m 1).ncard : ℝ) := by
  intro G _ Λ B d _ hB hfin α β t₀ hlim ε hε
  obtain ⟨t, ht0, ht⟩ : ∃ t, t₀ ≤ t ∧ 0 ≤ t := ⟨max t₀ 0, le_max_left _ _, le_max_right _ _⟩
  obtain ⟨η, hη, hβη⟩ : ∃ η : ℝ, 0 < η ∧ β * η < ε := by
    refine ⟨ε / (2 * (|β| + 1)), by positivity, ?_⟩
    have hpos : 0 < 2 * (|β| + 1) := by positivity
    have hηe : ε / (2 * (|β| + 1)) * (2 * (|β| + 1)) = ε := div_mul_cancel₀ _ hpos.ne'
    have hη : 0 < ε / (2 * (|β| + 1)) := by positivity
    have hb : β * (ε / (2 * (|β| + 1))) ≤ |β| * (ε / (2 * (|β| + 1))) :=
      mul_le_mul_of_nonneg_right (le_abs_self β) hη.le
    nlinarith [mul_nonneg (abs_nonneg β) hη.le]
  have hw := ((hlim t ht0).const_mul 2).sub (hlim (2 * t + η) (by linarith))
  have hlt : α - ε < 2 * (α + β * t) - (α + β * (2 * t + η)) := by
    have : 2 * (α + β * t) - (α + β * (2 * t + η)) = α - β * η := by ring
    rw [this]; linarith
  have ev1 := hw.eventually (lt_mem_nhds hlt)
  have ev2 : ∀ᶠ m : ℕ in atTop, Real.log 12 ≤ η * m :=
    (tendsto_natCast_atTop_atTop.const_mul_atTop hη).eventually_ge_atTop _
  filter_upwards [ev1, ev2, eventually_ge_atTop 1] with m h1 h2 hm
  have hmpos : (0:ℝ) < m := by exact_mod_cast hm
  have hmd : (0:ℝ) < (m:ℝ) ^ d := pow_pos hmpos d
  have he : 1 ≤ Real.exp (t * m) := Real.one_le_exp (mul_nonneg ht hmpos.le)
  have h12 : 12 ≤ Real.exp (η * m) := by
    rw [← Real.exp_log (by norm_num : (0:ℝ) < 12)]; exact Real.exp_le_exp.mpr h2
  have hE : (⌈2 * Real.exp (t * m)⌉₊ : ℝ) ^ 2 + (⌈2 * Real.exp (t * m)⌉₊ : ℝ) / 2 ≤
      Real.exp ((2 * t + η) * m) := by
    have hc : (⌈2 * Real.exp (t * m)⌉₊ : ℝ) ≤ 3 * Real.exp (t * m) := by
      have := Nat.ceil_lt_add_one (show 0 ≤ 2 * Real.exp (t * m) by linarith); linarith
    have hc0 : (0:ℝ) ≤ ⌈2 * Real.exp (t * m)⌉₊ := Nat.cast_nonneg _
    rw [show (2 * t + η) * (m:ℝ) = t * m + t * m + η * m by ring, Real.exp_add, Real.exp_add]
    nlinarith [mul_le_mul hc hc hc0 (by linarith), mul_le_mul_of_nonneg_left h12
      (mul_nonneg (by linarith : (0:ℝ) ≤ Real.exp (t * m)) (by linarith : (0:ℝ) ≤ Real.exp (t * m)))]
  have hsq := (hB m).ncard_sq_le_of_ceil (hfin m) he hE
  have hpos : ∀ R, 0 ≤ R → (0:ℝ) < (B m R).ncard := fun R hR => by
    have := (Set.ncard_pos (hfin m R)).mpr ⟨0, (hB m).zero_mem R hR⟩
    exact_mod_cast this
  have hlog := Real.log_le_log (pow_pos (hpos _ (by linarith)) 2) hsq
  rw [Real.log_pow, Real.log_mul (hpos 1 zero_le_one).ne' (hpos _ (Real.exp_pos _).le).ne'] at hlog
  push_cast at hlog
  have hdiv : (2 * Real.log ((B m (Real.exp (t * m))).ncard) - Real.log ((B m (Real.exp ((2 * t + η) * m))).ncard))
      / (m:ℝ) ^ d ≤ Real.log ((B m 1).ncard) / (m:ℝ) ^ d :=
    div_le_div_of_nonneg_right (by linarith) hmd.le
  rw [sub_div, mul_div_assoc] at hdiv
  rw [← le_div_iff₀ hmd]
  linarith

end GlobalTheory.VolBr
