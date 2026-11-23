import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.VolumeInputs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.MoriwakiSt
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small Filter Topology

namespace GlobalTheory.CompanionTheory.Ar.Small

theorem coef_sub_smul {Ψ : Type} [Fintype Ψ] {N : ℕ} (R : RootModel Ψ N) (lam nu : Wt Ψ N) (s : ℝ)
    (j : Option (Ψ × Fin N)) :
    R.coef (lam - s • nu) s j = R.coef lam 0 j - s * R.coef nu (-1) j := by
  rcases j with _ | ⟨a, i⟩
  · change s / (R.kA : ℝ) = 0 / (R.kA : ℝ) - s * ((-1) / (R.kA : ℝ))
    ring
  · change -(lam a i - s * nu a i) = -lam a i - s * -nu a i
    ring

theorem line_a_eq {Ψ : Type} [Fintype Ψ] {N : ℕ} (R : RootModel Ψ N) (t : ℝ) (j : Option (Ψ × Fin N)) :
    (R.line t j).a = (R.line 1 j).a := by
  rcases j with _ | r
  · rfl
  · change (R.x t r).a = (R.x 1 r).a
    rw [R.x_deg, R.x_deg]

theorem combLine_line_a {Ψ : Type} [Fintype Ψ] {N : ℕ} (R : RootModel Ψ N) (t : ℝ)
    (m : Option (Ψ × Fin N) → ℤ) (x : R.K) :
    (combLine (R.line t) m).a x = ∑ j, m j * (R.line 1 j).a x := by
  simp only [GlobalTheory.CompanionTheory.Ar.Top.combLine, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [line_a_eq R t j]

theorem FinBounds.mul_nat {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    {y : (Σ k, ι k) → Ω} {I : Type} [Fintype I] {w : I → Ω} {a₁ a' aτ aσ : K → ℤ} {τ σ : Ω}
    {q m₁ m₂ : ℕ} {u : MRing ι} {p : ℕ} [Fact p.Prime] {e a b : ℝ}
    (h : FinBounds y w a₁ a' aτ aσ τ σ q m₁ m₂ u p e a b) (t : ℕ) :
    FinBounds y w a₁ a' aτ aσ τ σ (q * t) (m₁ * t) (m₂ * t) u p e a b := by
  unfold GlobalTheory.CompanionTheory.Ar.Small.FinBounds at h ⊢
  intro z hz hu
  obtain ⟨r₁, r', rτ, rσ, E, φ, h1, h2, h3, h4, heq, rest⟩ := h z hz hu
  refine ⟨r₁, r', rτ, rσ, E, φ, h1, h2, h3, h4, ?_, rest⟩
  rw [pow_mul, pow_mul, pow_mul, pow_mul, heq, mul_pow, mul_pow]

theorem combLine_h_eq_exp {Ψ : Type} [Fintype Ψ] {N : ℕ} (R : RootModel Ψ N) (t : ℝ) (lam : Wt Ψ N) (s : ℝ)
    (q : ℕ) (m : Option (Ψ × Fin N) → ℤ) (hm : ∀ j, (m j : ℝ) = q * R.coef lam s j)
    (z : (Σ k, R.ι k) → ℂ) (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    (combLine (R.line t) m).h z = Real.exp (q * R.weight t lam s z) := by
  have hpos : ∀ j, 0 < (R.line t j).h z := fun j => (R.line t j).pos z hz
  simp only [GlobalTheory.CompanionTheory.Ar.Top.combLine, GlobalTheory.CompanionTheory.Ar.Top.RootModel.weight]
  rw [Finset.mul_sum, Real.exp_sum]
  refine Finset.prod_congr rfl (fun j _ => ?_)
  rw [← Real.rpow_intCast, Real.rpow_def_of_pos (hpos j), hm j]
  congr 1
  ring

theorem hasInputs_of_data : ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (R : RootModel Ψ N) (Λ : ℝ) (G : GenModel R Λ) (lam nu : Wt Ψ N) (n' n₀ : Option (Ψ × Fin N) → ℤ) (q₀ μ k : ℕ) (a₁ aτ aσ : R.K → ℤ) (τ σ ε : R.Ω) (u : MRing R.ι) (S : Finset ℕ) (e a b c : ℕ → ℝ) (A P R₀ cinf cc C s₀ : ℝ) (κ : (G.F →+* ℂ) → ℝ) (h₁ h' hτ hσ ρ : ((Σ k, R.ι k) → ℂ) → ℝ), 0 < q₀ → 0 < μ → (∀ j, (n' j : ℝ) = R.coef lam 0 j) → (∀ j, (n₀ j : ℝ) = q₀ * R.coef nu (-1) j) → (∀ x, ((8 * μ : ℕ) : ℤ) * a₁ x = ((8 * μ : ℕ) : ℤ) * (combLine (R.line 1) n').a x + ((3 * μ : ℕ) : ℤ) * aτ x + k * aσ x) → τ ≠ 0 → σ ≠ 0 → ε ≠ 0 → ε ∈ chartLatNm R.y (combLine (R.line 1) n₀).a 1 → IsFormOff (mCoordIdeal R.y) u → (∀ p ∈ S, p.Prime) → (∀ p, 0 ≤ c p) → (∀ p, p ∉ S → c p = 0) → (∀ p : ℕ, p.Prime → (((8 * μ : ℕ) : ℝ) * (e p + a p) + k * b p) * Real.log p ≤ ((8 * μ : ℕ) : ℝ) * c p) → (∀ (p : ℕ) [Fact p.Prime], FinBounds R.y G.w a₁ (combLine (R.line 1) n').a aτ aσ τ σ (8 * μ) (3 * μ) k u p (e p) (a p) (b p)) → (∀ sg, κ (NumberField.ComplexEmbedding.conjugate sg) = κ sg) → (∀ sg : G.F →+* ℂ, ∀ z ∈ mcPts (mCoordIdeal R.y), LiesOver R.y sg z → aeval z u ≠ 0 → 0 < h₁ z ∧ 0 < h' z ∧ 0 < hτ z ∧ 0 < hσ z ∧ h₁ z ^ (8 * μ) = h' z ^ (8 * μ) * hτ z ^ (3 * μ) * hσ z ^ k ∧ (∀ v : G.I → ℂ, (∀ i, HasVal R.y a₁ (G.w i) z (v i)) → v ≠ 0 ∧ Real.exp (-(A + 3 * ρ z) / 2) * h₁ z ≤ G.L.h fun x => v x.2) ∧ ValLe R.y aτ τ z (Real.exp (4 * (2 * P - ρ z) + R₀) * hτ z) ∧ ValLe R.y aσ σ z (Real.exp (κ sg) * hσ z)) → 0 ≤ C → 0 < s₀ → (∀ s : ℝ, 0 < s → s ≤ s₀ → ∀ z ∈ mcPts (mCoordIdeal R.y), aeval z u ≠ 0 → ∀ x : ℂ, HasVal R.y (combLine (R.line 1) n₀).a ε z x → x ≠ 0 → s / q₀ * Real.log ‖x‖ + R.weight (scale s) (lam - s • nu) s z ≤ C * s + Real.log (h' z)) → ((8 * μ : ℕ) : ℝ) * (A / 2 + 3 * P) + ((3 * μ : ℕ) : ℝ) * R₀ + k * embMean κ ≤ ((8 * μ : ℕ) : ℝ) * cinf → ∑ p ∈ S, c p + cinf ≤ cc → G.HasInputs (fun s => lam - s • nu) cc := by
  intro Ψ _ N R Λ G lam nu n' n₀ q₀ μ k a₁ aτ aσ τ σ ε u S e a b c A P R₀ cinf cc C s₀ κ h₁ h' hτ hσ ρ
    hq₀ hμ hn' hn₀ hdeg hτ0 hσ0 hε0 hεint hu hS hc0 hcS hcge hfin hκ harch hC hs₀ hmain hcinf hcc
  have hq₀' : (0:ℝ) < q₀ := by exact_mod_cast hq₀
  have hμ' : (0:ℝ) < μ := by exact_mod_cast hμ
  have h8μ : (0:ℝ) < 8 * μ := by linarith
  obtain ⟨N₀, hN₀, hN₀1⟩ : ∃ N₀ : ℕ, (q₀:ℝ) / (8 * μ) / s₀ < N₀ ∧ 1 ≤ N₀ :=
    ⟨⌈(q₀:ℝ) / (8 * μ) / s₀⌉₊ + 1, by push_cast; linarith [Nat.le_ceil ((q₀:ℝ) / (8 * μ) / s₀)], by omega⟩
  refine ⟨C, hC, fun n => (q₀:ℝ) / (8 * μ) / ((n + N₀ : ℕ) : ℝ), ?_, ?_, ?_⟩
  · intro n
    have hpos : (0:ℝ) < ((n + N₀ : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < n + N₀)
    exact div_pos (div_pos hq₀' h8μ) hpos
  · exact (tendsto_const_div_atTop_nhds_zero_nat ((q₀:ℝ) / (8 * μ))).comp (tendsto_add_atTop_nat N₀)
  intro n
  dsimp only
  have htN : N₀ ≤ n + N₀ := by omega
  generalize n + N₀ = t at htN ⊢
  have ht' : (0:ℝ) < t := by exact_mod_cast (by omega : 0 < t)
  have ht0 : (0:ℝ) ≤ t := ht'.le
  have hspos : 0 < (q₀:ℝ) / (8 * μ) / t := div_pos (div_pos hq₀' h8μ) ht'
  have hsle : (q₀:ℝ) / (8 * μ) / t ≤ s₀ := by
    rw [div_le_iff₀ ht']
    have h1 : (q₀:ℝ) / (8 * μ) / s₀ < t := lt_of_lt_of_le hN₀ (by exact_mod_cast htN)
    have h2 := (div_lt_iff₀ hs₀).mp h1
    linarith
  have hqs : ((8 * μ * t : ℕ) : ℝ) * ((q₀:ℝ) / (8 * μ) / t) = q₀ := by
    have hμne : (μ:ℝ) ≠ 0 := hμ'.ne'
    have htne : (t:ℝ) ≠ 0 := ht'.ne'
    push_cast
    field_simp
  have hm : ∀ j, ((((8 * μ * t : ℕ) : ℤ) * n' j - n₀ j : ℤ) : ℝ) =
      ((8 * μ * t : ℕ) : ℝ) * R.coef (lam - ((q₀:ℝ) / (8 * μ) / t) • nu) ((q₀:ℝ) / (8 * μ) / t) j := by
    intro j
    rw [coef_sub_smul, ← hn' j]
    have h0 := hn₀ j
    have hqs' := hqs
    push_cast at h0 hqs' ⊢
    linear_combination (-1:ℝ) * h0 + R.coef nu (-1) j * hqs'
  refine ⟨8 * μ * t, fun j => ((8 * μ * t : ℕ) : ℤ) * n' j - n₀ j,
    Nat.mul_pos (Nat.mul_pos (by norm_num) hμ) (by omega), hm, ⟨?_⟩⟩
  refine GlobalTheory.CompanionTheory.Ar.Small.SectionInputs.mk a₁ (combLine (R.line 1) n').a aτ aσ (combLine (R.line 1) n₀).a τ σ ε
    (3 * μ * t) (k * t) 1 u S e a b c A P R₀ κ cinf G.L_deg ?_ ?_ (by ring) hτ0 hσ0 hε0 hεint hu hS hc0 hcS ?_
    ?_ hκ ?_ ?_ hcc
  · intro x
    have h0 := hdeg x
    push_cast at h0 ⊢
    linear_combination (t:ℤ) * h0
  · intro x
    rw [combLine_line_a R 1 n' x, combLine_line_a R 1 n₀ x, combLine_line_a R _ _ x,
      Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    push_cast
    ring
  · intro p hp
    calc _ = (t:ℝ) * ((((8 * μ : ℕ) : ℝ) * (e p + a p) + k * b p) * Real.log p) := by push_cast; ring
      _ ≤ (t:ℝ) * (((8 * μ : ℕ) : ℝ) * c p) := mul_le_mul_of_nonneg_left (hcge p hp) ht0
      _ = _ := by push_cast; ring
  · intro p _
    exact (hfin p).mul_nat t
  · intro sg
    unfold GlobalTheory.CompanionTheory.Ar.Small.ArchBounds
    intro z hz hlies hu'
    obtain ⟨p1, p2, p3, p4, hpow, hv, hτv, hσv⟩ := harch sg z hz hlies hu'
    refine ⟨h₁ z, h' z, hτ z, hσ z, ρ z, p1, p2, p3, p4, ?_, hv, hτv, hσv, ?_⟩
    · rw [pow_mul (h₁ z) (8 * μ) t, pow_mul (h' z) (8 * μ) t, pow_mul (hτ z) (3 * μ) t, pow_mul (hσ z) k t,
        hpow, mul_pow, mul_pow]
    · intro x hx
      by_cases hx0 : x = 0
      · rw [hx0, norm_zero, pow_one, zero_mul]
        positivity
      · have hM := combLine_h_eq_exp R (scale ((q₀:ℝ) / (8 * μ) / t)) (lam - ((q₀:ℝ) / (8 * μ) / t) • nu)
          ((q₀:ℝ) / (8 * μ) / t) (8 * μ * t) _ hm z hz.1
        have hmn := hmain _ hspos hsle z hz hu' x hx hx0
        have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
        have hq0 : (0:ℝ) ≤ ((8 * μ * t : ℕ) : ℝ) := Nat.cast_nonneg _
        have hq1 : ((8 * μ * t : ℕ) : ℝ) * ((q₀:ℝ) / (8 * μ) / t / q₀) = 1 := by
          rw [← mul_div_assoc, hqs, div_self hq₀'.ne']
        have key := mul_le_mul_of_nonneg_left hmn hq0
        rw [mul_add, ← mul_assoc, hq1, one_mul, mul_add] at key
        have hexp : Real.exp (((8 * μ * t : ℕ) : ℝ) * Real.log (h' z)) = h' z ^ (8 * μ * t) := by
          rw [Real.exp_nat_mul, Real.exp_log p2]
        rw [hM, pow_one, ← hexp, ← Real.exp_add, ← Real.exp_log hxpos, ← Real.exp_add]
        exact Real.exp_le_exp.mpr key
  · calc _ = (t:ℝ) * (((8 * μ : ℕ) : ℝ) * (A / 2 + 3 * P) + ((3 * μ : ℕ) : ℝ) * R₀ + k * embMean κ) := by
          push_cast; ring
      _ ≤ (t:ℝ) * (((8 * μ : ℕ) : ℝ) * cinf) := mul_le_mul_of_nonneg_left hcinf ht0
      _ = _ := by push_cast; ring

end GlobalTheory.CompanionTheory.Ar.Small
