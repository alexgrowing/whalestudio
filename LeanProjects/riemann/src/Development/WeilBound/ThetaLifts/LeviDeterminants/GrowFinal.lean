import Development.WeilBound.ThetaLifts.LeviDeterminants.GrowInt

noncomputable section

namespace PositivityTheory.ThKF0.Grow

open scoped Matrix NNReal ENNReal Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {ψ : AddChar (AF F) ℂ}

theorem dR_mult (hψ : IsStd ψ) (b : V F κ) (Θ : (κ → AF F) → ℂ) (x : κ → AF F) :
    dR ψ (0, b) Θ x = -(2 * Real.pi * Complex.I) * (linForm b fun i => evI F (x i) : ℝ) * Θ x := by
  have e : ∀ t : ℝ, schr ψ (emb (t • ((0, b) : V F κ × V F κ))) Θ x =
      Complex.exp (-(2 * Real.pi * Complex.I) * (linForm b fun i => evI F (x i) : ℝ) * t) * Θ x := fun t => by
    have h0 : (emb ((0, b) : V F κ × V F κ)).1 = 0 := congrArg Prod.fst (emb_zero (F := F) (κ := κ))
    have := phase_line ψ hψ 0 _ x (at_inf b) t
    simp only [evI_inf, Pi.zero_apply, evI_zero, zero_mul, Finset.sum_const_zero, mul_zero, map_zero, add_zero] at this
    rw [emb_smul, schr, Prod.smul_fst, Prod.smul_snd, h0]
    change ψ (x ⬝ᵥ (realAd F t • fun i => inf (b i)) + _ * (_ ⬝ᵥ (realAd F t • fun i => inf (b i)))) * _ = _
    rw [this, smul_zero, add_zero]
    push_cast
    ring_nf
  simp only [dR, e]
  have := ((((hasDerivAt_id (0 : ℝ)).ofReal_comp).const_mul
    (-(2 * Real.pi * Complex.I) * (linForm b fun i => evI F (x i) : ℝ))).cexp).mul_const (Θ x)
  simpa using this.deriv

theorem word_mult (hψ : IsStd ψ) (b : V F κ) (j : ℕ) (Θ : (κ → AF F) → ℂ) (x : κ → AF F) :
    word ψ (List.replicate j (0, b)) Θ x = (-(2 * Real.pi * Complex.I) * (linForm b fun i => evI F (x i) : ℝ)) ^ j * Θ x := by
  induction j with
  | zero => simp [word]
  | succ j ih =>
    change dR ψ (0, b) (word ψ (List.replicate j (0, b)) Θ) x = _
    rw [dR_mult hψ, ih, pow_succ', mul_assoc (_ * _)]

theorem word_lev (hψ : IsStd ψ) (l : List (V F κ × V F κ)) {Θ : (κ → AF F) → ℂ} (hΘ : Θ ∈ schA F κ) {m : ℕ} (h : Lev m Θ) :
    Lev m (word ψ l Θ) := by
  induction l with
  | nil => exact h
  | cons w l ih => exact (derivOK F κ ψ hψ w _ (word_mem hψ l hΘ)).2.2 m ih

theorem list_bound (hψ : IsStd ψ) {μ : @Measure (κ → AF F) (borel _)} (hμ : IsHaar μ) {Φ : (κ → AF F) → ℂ}
    (hΦ : Φ ∈ schA F κ) (j : ℕ) (S : List (List (V F κ × V F κ))) : ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∃ k : ℕ,
      ∀ T s d (y : ℝ≥0), 1 ≤ y → Impl ψ T s → Bd s d y → ∀ b : V F κ, ‖b‖ ≤ 1 →
        (S.map fun l => nsq μ (word ψ l (word ψ (List.replicate j (0, b)) (T Φ)))).sum ≤ C * (y : ℝ≥0∞) ^ k := by
  induction S with
  | nil => exact ⟨0, by simp, 0, by simp⟩
  | cons l S ih =>
    obtain ⟨C, hC, k, h⟩ := ih
    obtain ⟨C', hC', h'⟩ := word_bound hψ hμ (l.length + j) Φ hΦ
    obtain ⟨R, hR1, hR⟩ : ∃ R : ℝ≥0, 1 ≤ R ∧ ∀ w ∈ l, ‖w‖ ≤ R :=
      ⟨1 + (l.map nnnorm).sum, le_self_add, fun w hw => by
        have : ‖w‖₊ ≤ (l.map nnnorm).sum := List.single_le_sum (fun _ _ => zero_le) _ (List.mem_map_of_mem hw)
        exact NNReal.coe_le_coe.2 (this.trans le_add_self)⟩
    refine ⟨C' * (R : ℝ≥0∞) ^ (2 * (l.length + j)) + C, by finiteness, 2 * (l.length + j) + k,
      fun T s d y hy hT hs b hb => ?_⟩
    obtain ⟨l', h1, h2, h3⟩ := hT.word hψ hμ y.2 hs hΦ R (l ++ List.replicate j (0, b)) fun w hw => by
      rcases List.mem_append.1 hw with hw | hw
      · exact hR w hw
      · rw [List.eq_of_mem_replicate hw, Prod.norm_mk, norm_zero]
        exact max_le R.2 (hb.trans hR1)
    have hy' : (1 : ℝ≥0∞) ≤ y := by exact_mod_cast hy
    rw [List.map_cons, List.sum_cons, add_mul]
    refine add_le_add ?_ ((h T s d y hy hT hs b hb).trans (mul_le_mul' le_rfl (pow_le_pow_right₀ hy' le_add_self)))
    have e : word ψ l (word ψ (List.replicate j (0, b)) (T Φ)) = T (word ψ l' Φ) := by
      rw [h3, word, word, word, List.foldr_append]
    rw [e, hT.unit μ hμ _ (word_mem hψ l' hΦ)]
    refine (h' l' (by simpa using h1) (y * R) h2).trans ?_
    rw [ENNReal.coe_mul, mul_pow, mul_comm ((y : ℝ≥0∞) ^ _), ← mul_assoc]
    exact mul_le_mul' le_rfl (pow_le_pow_right₀ hy' le_self_add)

theorem core (hF : FinInv) (hS : Sob) (hψ : IsStd ψ) {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) (j : ℕ) :
    ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ T s (d : ℕ) (y : ℝ), 1 ≤ d → (d : ℝ) ≤ y → Impl ψ T s → Bd s d y → ∀ b : V F κ, ‖b‖ ≤ 1 →
      ∀ x, ‖word ψ (List.replicate j (0, b)) (T Φ) x‖ ≤ C * y ^ k := by
  obtain ⟨μ, hμ, S, C, k, h⟩ := hS F κ ψ hψ
  obtain ⟨m₀, hm₀, h₀⟩ := hF F κ ψ hψ Φ hΦ
  obtain ⟨C', hC', k', h'⟩ := list_bound hψ hμ hΦ j S
  lift C' to ℝ≥0 using hC'
  refine ⟨1 + C * m₀ ^ k * C', k + k', by positivity, fun T s d y hd hy hT hs b hb x => ?_⟩
  have hy1 : (1 : ℝ) ≤ y := le_trans (by exact_mod_cast hd) hy
  lift y to ℝ≥0 using zero_le_one.trans hy1
  have lev : Lev (m₀ * d) (T Φ) := fun u hu x => by
    have := congrFun (h₀ T s d y hT hs (u, 0) ⟨hu, fun _ => ⟨rfl, fun v => by simp⟩⟩) x
    simpa [schr] using this
  have h1 := (h (m₀ * d) (Nat.mul_pos hm₀ hd) _ (word_mem hψ _ (hT.pres _ hΦ))
    (word_lev hψ (List.replicate j (0, b)) (hT.pres _ hΦ) lev) x).trans
    (mul_le_mul' le_rfl (h' T s d y (by exact_mod_cast hy1) hT hs b hb))
  rw [enorm_eq_nnnorm] at h1
  have h2 : ‖word ψ (List.replicate j (0, b)) (T Φ) x‖ ^ 2 ≤ C * ((m₀ : ℝ) * d) ^ k * (C' * (y : ℝ) ^ k') := by
    exact_mod_cast h1
  have h3 : C * ((m₀ : ℝ) * d) ^ k * (C' * (y : ℝ) ^ k') ≤ C * m₀ ^ k * C' * (y : ℝ) ^ (k + k') := by
    calc _ ≤ C * ((m₀ : ℝ) * y) ^ k * (C' * (y : ℝ) ^ k') := by gcongr
      _ = _ := by ring
  have h4 : (1 : ℝ) ≤ (y : ℝ) ^ (k + k') := one_le_pow₀ hy1
  rw [add_mul]
  nlinarith [sq_nonneg (‖word ψ (List.replicate j (0, b)) (T Φ) x‖ - 1), norm_nonneg (word ψ (List.replicate j (0, b)) (T Φ) x)]

theorem weighted (hF : FinInv) (hS : Sob) (hT : TrBd) (hψ : IsStd ψ) {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) (N : ℕ) :
    ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ T s (d : ℕ) (y : ℝ), 1 ≤ d → (d : ℝ) ≤ y → Impl ψ T s → Bd s d y →
      ∀ x, ‖T Φ x‖ * (1 + ‖fun i => evI F (x i)‖) ^ N ≤ C * y ^ k := by
  obtain ⟨C₀, k₀, p₀, h₀⟩ := core hF hS hψ hΦ 0
  obtain ⟨C₁, k₁, p₁, h₁⟩ := core hF hS hψ hΦ N
  obtain ⟨c, hc, hb⟩ := hT F κ
  refine ⟨2 ^ (N - 1) * (C₀ + c ^ N * C₁), k₀ + k₁, by positivity, fun T s d y hd hy hI hs x => ?_⟩
  have hy1 : (1 : ℝ) ≤ y := le_trans (by exact_mod_cast hd) hy
  obtain ⟨b, hb1, hb2⟩ := hb fun i => evI F (x i)
  have a₀ : ‖T Φ x‖ ≤ C₀ * y ^ k₀ := h₀ T s d y hd hy hI hs b hb1 x
  have a₁ := h₁ T s d y hd hy hI hs b hb1 x
  rw [word_mult hψ, norm_mul, norm_pow, norm_mul, Complex.norm_real, Real.norm_eq_abs, linForm_apply] at a₁
  have hπ : (1 : ℝ) ≤ ‖-(2 * Real.pi * Complex.I : ℂ)‖ := by
    simp only [norm_neg, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_ofNat, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
    linarith [Real.pi_gt_three]
  have a₂ : ‖T Φ x‖ * ‖fun i => evI F (x i)‖ ^ N ≤ c ^ N * (C₁ * y ^ k₁) := by
    refine le_trans ?_ (mul_le_mul_of_nonneg_left a₁ (by positivity))
    rw [← mul_assoc, ← mul_pow, mul_comm]
    refine mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hb2.trans ?_) N) (norm_nonneg _)
    exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (abs_nonneg _) hπ) hc
  have e₀ : y ^ k₀ ≤ y ^ (k₀ + k₁) := pow_le_pow_right₀ hy1 le_self_add
  have e₁ : y ^ k₁ ≤ y ^ (k₀ + k₁) := pow_le_pow_right₀ hy1 le_add_self
  calc _ ≤ ‖T Φ x‖ * (2 ^ (N - 1) * (1 ^ N + ‖fun i => evI F (x i)‖ ^ N)) :=
        mul_le_mul_of_nonneg_left (add_pow_le zero_le_one (norm_nonneg _) N) (norm_nonneg _)
    _ = 2 ^ (N - 1) * (‖T Φ x‖ + ‖T Φ x‖ * ‖fun i => evI F (x i)‖ ^ N) := by ring
    _ ≤ 2 ^ (N - 1) * (C₀ * y ^ (k₀ + k₁) + c ^ N * (C₁ * y ^ (k₀ + k₁))) :=
        mul_le_mul_of_nonneg_left (add_le_add (a₀.trans (mul_le_mul_of_nonneg_left e₀ p₀))
          (a₂.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left e₁ p₁) (pow_nonneg hc N)))) (by positivity)
    _ = _ := by ring

open GlobalTheory.LFun GlobalTheory.ThK in
theorem weil_rep_rapid_decay_of_growth (hA : HtBd) (hF : FinInv) (hS : Sob) (hT : TrBd) : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ Φ ∈ schA F (Fin n × Fin d), ∀ N : ℕ, ∃ (C : ℝ) (k : ℕ), ∀ g h (x : Fin n × Fin d → AF F),
    ‖om (g, h) Φ x‖ * (1 + ‖fun i => evI F (x i)‖) ^ N ≤ C * ((ht g : ℝ) * ht h) ^ k := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP Φ hΦ N
  obtain ⟨C, -, hC⟩ := hA F E σ n d X W M
  obtain ⟨C', k, -, h⟩ := weighted hF hS hT hP.base.std hΦ N
  refine ⟨C' * C ^ k, k, fun g g' x => ?_⟩
  obtain ⟨m, h1, h2, h3⟩ := hC g g'
  rw [mul_assoc, ← mul_pow]
  exact h _ _ m _ h1 h2 (impl_sOf hP.weil g g') h3 x

end PositivityTheory.ThKF0.Grow
