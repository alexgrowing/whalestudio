import ReciprocityTheory.ReductiveGroups.DiscreteSeries.InfinitesimalDecay.DecBoundOfCompact
import Formalism.HermitianCurvature.BesselNonvanishingReduction
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.ZhatNormLinearBound
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.AdmissibleOfIwasawa
import CompanionTheory.AutomorphicTheory.KFiniteVectors.KDecay

open Matrix Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData ReciprocityTheory.ChartRestriction.DS
open scoped InnerProductSpace

noncomputable section

namespace CompanionTheory.FamilyDerivativeExpansion.DecS

lemma dsigW_eq {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Mx k r → (H →L[ℂ] H)) :
    ∀ (W : List (Mx k r)) (v : H),
      Formalism.MainNotions.S.dsigW (k := k) (r := r) σ W v = PI.UpqRep.dsigW (k := k) (r := r) σ W v
  | [], _ => rfl
  | X :: W, v => by
    show Formalism.MainNotions.S.dsig (k := k) (r := r) σ X (Formalism.MainNotions.S.dsigW σ W v) = PI.UpqRep.dsig (k := k) (r := r) σ X (PI.UpqRep.dsigW σ W v)
    rw [dsigW_eq σ W v]
    rfl

lemma thr_le {n : ℕ} (hn : 1 ≤ n) (ε : Fin n → Bool) : thrStar ε ≤ 40 * (n : ℝ) ^ 3 := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : (pOf ε : ℝ) ≤ n := by
    have : pOf ε ≤ n := by simpa [pOf] using Finset.card_filter_le Finset.univ (fun a => ε a = true)
    exact_mod_cast this
  have hq : (qOf ε : ℝ) ≤ n := by
    have : qOf ε ≤ n := by simpa [qOf] using Finset.card_filter_le Finset.univ (fun a => ε a = false)
    exact_mod_cast this
  have hq0 : (S7.q0 ε : ℝ) ≤ n := le_trans (by exact_mod_cast min_le_left _ _) hp
  have h0 : (0 : ℝ) ≤ S7.q0 ε := Nat.cast_nonneg _
  have hp0 : (0 : ℝ) ≤ pOf ε := Nat.cast_nonneg _
  have hq1 : (0 : ℝ) ≤ qOf ε := Nat.cast_nonneg _
  have e2 : (n : ℝ) ≤ n ^ 2 := by nlinarith
  have e3 : (n : ℝ) ^ 2 ≤ n ^ 3 := by nlinarith
  have h1 : (n : ℝ) * pOf ε * qOf ε ≤ n ^ 3 := by
    calc (n : ℝ) * pOf ε * qOf ε ≤ n * n * n := by gcongr
      _ = n ^ 3 := by ring
  have h2 : √(2 * (S7.q0 ε : ℝ)) ≤ 2 * n := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith
  have h3 : (n : ℝ) * S7.q0 ε ≤ n ^ 2 := by nlinarith
  exact max_le (by linarith) (by nlinarith)

lemma room {n : ℕ} (hn : 1 ≤ n) (ε : Fin n → Bool) {h : ℝ} (hh : 120 * (n : ℝ) ^ 3 ≤ h) :
    thrStar ε + (h / 8 + 1) < h := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have := thr_le hn ε
  have := one_le_pow₀ (n := 3) hn'
  linarith

theorem decayM {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ} {h : ℝ}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {σ : Mx k r → (H →L[ℂ] H)}
    (hl : Formalism.QuantumDeterminants.IsHCParam lam) (hσ : PI.UpqRep.IsDSHpk k r ε lam σ) (hg : Formalism.QuantumDeterminants.GapAtLeast ε lam h)
    (m : ℕ) (hm : thrStar ε + m < h) (v0 : H) (hv0 : v0 ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ) :
    ∃ (C : ℝ) (Ws : List (List (Mx k r))), (∀ W ∈ Ws, ∀ X ∈ W, PI.UpqRep.InLieHpk k r X) ∧
      ∀ b : ℝ, b ≤ m → ∀ w ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ, ∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r),
        ‖⟪v0, σ x w⟫_ℂ‖ ≤ C * (Ws.map fun W => ‖PI.UpqRep.dsigW (k := k) (r := r) σ W w‖).sum * B.gN x ^ (-b) := by
  obtain ⟨C, Ws, hW, hb⟩ := ReciprocityTheory.ChartRestriction.DS.DecInf.decSm (k := k) (r := r) hl hg m hm (σ := σ) hσ
  simp only [dsigW_eq] at hb
  refine ⟨C * (Ws.map fun W => ‖PI.UpqRep.dsigW (k := k) (r := r) σ W v0‖).sum, Ws, fun W h1 X h2 => (hW W h1).2 X h2,
    fun b hba w hw x hx => ?_⟩
  have h1 := hb w hw v0 hv0 x hx
  have hN : 1 ≤ B.gN x := PI.PolynomialProperness.GN.gN_ge_one hx
  have hp : B.gN x ^ b ≤ B.gN x ^ m := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hN hba
  have hb0 : 0 < B.gN x ^ b := Real.rpow_pos_of_pos (by linarith) _
  rw [Real.rpow_neg (by linarith), ← div_eq_mul_inv, le_div_iff₀ hb0]
  calc ‖⟪v0, σ x w⟫_ℂ‖ * B.gN x ^ b ≤ B.gN x ^ m * ‖⟪v0, σ x w⟫_ℂ‖ := by
        rw [mul_comm]; exact mul_le_mul_of_nonneg_right hp (norm_nonneg _)
    _ ≤ _ := h1.trans (le_of_eq (by ring))

theorem decay {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ} {h : ℝ}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {σ : Mx k r → (H →L[ℂ] H)}
    (hl : Formalism.QuantumDeterminants.IsHCParam lam) (hσ : PI.UpqRep.IsDSHpk k r ε lam σ) (hg : Formalism.QuantumDeterminants.GapAtLeast ε lam h)
    (hh : 120 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 ≤ h) (v0 : H) (hv0 : v0 ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ) :
    ∃ (C : ℝ) (Ws : List (List (Mx k r))), (∀ W ∈ Ws, ∀ X ∈ W, PI.UpqRep.InLieHpk k r X) ∧
      ∀ b : ℝ, b ≤ aOf r h → ∀ w ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ, ∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r),
        ‖⟪v0, σ x w⟫_ℂ‖ ≤ C * (Ws.map fun W => ‖PI.UpqRep.dsigW (k := k) (r := r) σ W w‖).sum * B.gN x ^ (-b) := by
  have h0 : 0 ≤ h := le_trans (by positivity) hh
  have ha0 : 0 ≤ aOf r h := by unfold aOf; positivity
  have ha : aOf r h ≤ h / 8 := by
    unfold aOf
    have hs : (1 : ℝ) ≤ √(2 * ((r : ℝ) + 1)) := Real.one_le_sqrt.2 (by linarith [(Nat.cast_nonneg r : (0 : ℝ) ≤ r)])
    exact div_le_div_of_nonneg_left h0 (by norm_num) (by linarith)
  have hm : thrStar ε + (⌈aOf r h⌉₊ : ℕ) < h := by
    have := room (by omega) ε hh
    have := Nat.ceil_lt_add_one ha0
    linarith
  obtain ⟨C, Ws, h1, h2⟩ := decayM hl hσ hg _ hm v0 hv0
  exact ⟨C, Ws, h1, fun b hb => h2 b (hb.trans (Nat.le_ceil _))⟩

theorem decay_infinite_range : DecInf := by
  intro k r ε lam h H _ _ _ σ hl hσ hg hok v0 hv0
  obtain ⟨C, Ws, h1, h2⟩ := decay hl hσ hg hok.2.1 v0 (CompanionTheory.D.gk.admitted.k_finite_smooth k r ε lam H σ hl hσ v0 hv0)
  refine ⟨C, Ws, h1, fun w hw x hx => ?_⟩
  have := h2 (aOf r h - 1) (by linarith) w hw x hx
  rwa [neg_sub] at this

theorem decay_low_range : DecLow := by
  intro k r _ ε lam h H _ _ _ σ hl hσ hg hh P hP w₁ w₂ h₁ h₂
  have s := fun w hw => CompanionTheory.D.gk.admitted.k_finite_smooth k r ε lam H σ hl hσ w
    (MainStatements.BetaInf.isKFinHpk_of_low (lam := lam) (σ := σ) hP (w := w) hw)
  obtain ⟨C, Ws, -, h2⟩ := decay hl hσ hg hh w₂ (s _ h₂)
  exact ⟨_, fun x hx => h2 (aOf r h) le_rfl w₁ (s _ h₁) x hx⟩

end CompanionTheory.FamilyDerivativeExpansion.DecS
