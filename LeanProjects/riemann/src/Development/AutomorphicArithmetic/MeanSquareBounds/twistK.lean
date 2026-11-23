import Development.AutomorphicArithmetic.MeanSquareBounds.PrimeSetTwoBounds
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.MSqTwist
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTFinal
import Formalism.LandauZeroFreeBounds.SiegelWalfiszAPOfSiegelLower

open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

namespace QH

set_option maxHeartbeats 1000000 in
private theorem final_ineqK (A B ε c₀ c₃ A₀ C₀ L u lm ℓm ℓ : ℝ) (hA0 : 0 < A) (hB0 : 0 < B) (hε : 0 < ε) (hc₀ : 0 < c₀) (hc₃ : 0 < c₃)
    (hL1 : 2 ≤ L) (hL2 : 8 * (ε / 5 + 2 + B + Real.log 128) / c₀ ≤ L)
    (hL3 : 8 * (B + Real.log (32 * (|A₀| + 1))) / c₃ ≤ L) (hL4 : Real.log (32 * (|A₀| + 1)) ≤ L)
    (hL5 : 8 * |C₀| * (Real.log (6 + A) + ε / 5 + 1) ≤ L)
    (hu1 : (1 / 4) * L ^ 2 * ℓm ≤ u) (hu2 : (A / 4 + (B + 1) ^ 2 / c₃ + 5 * (B + 1)) * L ^ 3 ≤ u)
    (hlogu : Real.log u ≤ (ε / 5 + 2) * L)
    (hℓm : ℓm ≤ 4 * Real.exp (ε / 5 * L))
    (hlm0 : 2 ≤ lm) (hlm : lm ≤ ℓ) (hℓ : ℓ ≤ ℓm + A * L) :
    C₀ * lm * Real.log (lm + 2) ≤ u ∧
    16 * u * Real.exp (-(c₀ / ℓ * u)) ≤ Real.exp (-(B * L)) / 8 ∧
    2 * |A₀| * (Real.exp (-(c₃ * u / lm)) + Real.exp (-Real.sqrt (c₃ * u))) ≤ Real.exp (-(B * L)) / 8 ∧
    Real.exp (-(2 / 5 * u)) ≤ Real.exp (-(B * L)) / 4 := by
  have hL0 : 0 < L := by linarith
  have hu0 : 0 < u := by
    have : 0 < (A / 4 + (B + 1) ^ 2 / c₃ + 5 * (B + 1)) * L ^ 3 := by positivity
    linarith
  have h16 : 0 ≤ (B + 1) ^ 2 / c₃ * L ^ 3 := by positivity
  have h17 : 0 ≤ A * L ^ 3 := by positivity
  have h18 : 0 ≤ (B + 1) * L ^ 3 := by positivity
  have hu2' : (A / 4 + (B + 1) ^ 2 / c₃ + 5 * (B + 1)) * L ^ 3 = A * L ^ 3 / 4 + (B + 1) ^ 2 / c₃ * L ^ 3 + 5 * ((B + 1) * L ^ 3) := by ring
  have hP0 : L ^ 2 * ℓ / 8 ≤ u := by
    have : L ^ 2 * ℓ ≤ L ^ 2 * (ℓm + A * L) := mul_le_mul_of_nonneg_left hℓ (by positivity)
    have e : L ^ 2 * (ℓm + A * L) = L ^ 2 * ℓm + A * L ^ 3 := by ring
    linarith
  have hℓ0 : 0 < ℓ := by linarith
  have hP1 : L ^ 2 / 8 ≤ u / ℓ := by rw [le_div_iff₀ hℓ0]; linarith
  have hP2 : L ^ 2 / 8 ≤ u / lm := by
    have : u / ℓ ≤ u / lm := div_le_div_of_nonneg_left hu0.le (by linarith) hlm
    linarith
  have hQ : 0 ≤ Real.log (32 * (|A₀| + 1)) := Real.log_nonneg (by nlinarith [abs_nonneg A₀])
  have hl128 : 0 ≤ Real.log 128 := Real.log_nonneg (by norm_num)
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    have hA : lm + 2 ≤ (6 + A) * Real.exp ((ε / 5 + 1) * L) := by
      have ee : (ε / 5 + 1) * L = ε / 5 * L + L := by ring
      have hεL : 0 ≤ ε / 5 * L := by positivity
      have e1 : Real.exp (ε / 5 * L) ≤ Real.exp ((ε / 5 + 1) * L) := Real.exp_le_exp.mpr (by linarith)
      have e2 : L ≤ Real.exp ((ε / 5 + 1) * L) := by
        have := Real.add_one_le_exp L
        have : Real.exp L ≤ Real.exp ((ε / 5 + 1) * L) := Real.exp_le_exp.mpr (by linarith)
        linarith
      have e3 : 1 ≤ Real.exp ((ε / 5 + 1) * L) := Real.one_le_exp (by positivity)
      have e4 := mul_le_mul_of_nonneg_left e2 hA0.le
      linarith
    have hB : Real.log (lm + 2) ≤ Real.log (6 + A) + (ε / 5 + 1) * L := by
      calc Real.log (lm + 2) ≤ Real.log ((6 + A) * Real.exp ((ε / 5 + 1) * L)) := Real.log_le_log (by linarith) hA
        _ = _ := by rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp]
    have hl806 : 0 ≤ Real.log (6 + A) := Real.log_nonneg (by linarith)
    have hlog0 : 0 ≤ Real.log (lm + 2) := Real.log_nonneg (by linarith)
    have hC : |C₀| * Real.log (lm + 2) ≤ L ^ 2 / 8 := by
      have : |C₀| * Real.log (lm + 2) ≤ |C₀| * (Real.log (6 + A) + (ε / 5 + 1) * L) :=
        mul_le_mul_of_nonneg_left hB (abs_nonneg _)
      have : |C₀| * (Real.log (6 + A) + (ε / 5 + 1) * L) ≤ |C₀| * ((Real.log (6 + A) + ε / 5 + 1) * L) := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        have : Real.log (6 + A) ≤ Real.log (6 + A) * L := by nlinarith
        linarith
      have h5 := mul_le_mul_of_nonneg_right hL5 hL0.le
      have e5 : |C₀| * ((Real.log (6 + A) + ε / 5 + 1) * L) = (8 * |C₀| * (Real.log (6 + A) + ε / 5 + 1) * L) / 8 := by ring
      have e6 : L ^ 2 / 8 = L * L / 8 := by ring
      linarith
    calc C₀ * lm * Real.log (lm + 2) ≤ |C₀| * lm * Real.log (lm + 2) := by
          apply mul_le_mul_of_nonneg_right _ hlog0
          exact mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)
      _ = lm * (|C₀| * Real.log (lm + 2)) := by ring
      _ ≤ lm * (L ^ 2 / 8) := mul_le_mul_of_nonneg_left hC (by linarith)
      _ ≤ ℓ * (L ^ 2 / 8) := mul_le_mul_of_nonneg_right hlm (by positivity)
      _ ≤ u := by linarith
  · have hc : c₀ * L ^ 2 / 8 ≤ c₀ / ℓ * u := by
      have := mul_le_mul_of_nonneg_left hP1 hc₀.le
      have e1 : c₀ / ℓ * u = c₀ * (u / ℓ) := by ring
      have e2 : c₀ * L ^ 2 / 8 = c₀ * (L ^ 2 / 8) := by ring
      rw [e1, e2]; exact this
    have hk : (ε / 5 + 2 + B) * L + Real.log 128 ≤ c₀ * L ^ 2 / 8 := by
      have h8 : 8 * (ε / 5 + 2 + B + Real.log 128) ≤ c₀ * L := by rwa [div_le_iff₀ hc₀, mul_comm L] at hL2
      have h9 := mul_le_mul_of_nonneg_right h8 hL0.le
      have : Real.log 128 ≤ Real.log 128 * L := by nlinarith
      have e : c₀ * L ^ 2 / 8 = c₀ * L * L / 8 := by ring
      linarith
    have hlu : u = Real.exp (Real.log u) := (Real.exp_log hu0).symm
    calc 16 * u * Real.exp (-(c₀ / ℓ * u)) ≤ 16 * Real.exp ((ε / 5 + 2) * L) * Real.exp (-(c₀ * L ^ 2 / 8)) := by
          gcongr
          rw [hlu]; exact Real.exp_le_exp.mpr hlogu
      _ = Real.exp ((ε / 5 + 2) * L - c₀ * L ^ 2 / 8 + Real.log 16) := by
          rw [Real.exp_add, Real.exp_log (by norm_num), sub_eq_add_neg, Real.exp_add]; ring
      _ ≤ Real.exp (-(B * L) - Real.log 8) := Real.exp_le_exp.mpr (by
          have : Real.log 128 = Real.log 16 + Real.log 8 := by
            rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
          linarith)
      _ = Real.exp (-(B * L)) / 8 := by rw [Real.exp_sub, Real.exp_log (by norm_num)]
  · set Q := 32 * (|A₀| + 1)
    have hQ0 : 0 < Q := by positivity
    have hA : 2 * |A₀| ≤ Q / 16 := by simp only [Q]; linarith [abs_nonneg A₀]
    have key : ∀ t : ℝ, B * L + Real.log Q ≤ t → 2 * |A₀| * Real.exp (-t) ≤ Real.exp (-(B * L)) / 16 := by
      intro t ht
      calc 2 * |A₀| * Real.exp (-t) ≤ Q / 16 * Real.exp (-t) := mul_le_mul_of_nonneg_right hA (Real.exp_pos _).le
        _ ≤ Q / 16 * Real.exp (-(B * L) - Real.log Q) :=
            mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by positivity)
        _ = Real.exp (-(B * L)) / 16 := by
            rw [Real.exp_sub, Real.exp_log hQ0]; field_simp
    have t1 : B * L + Real.log Q ≤ c₃ * u / lm := by
      have : 8 * (B + Real.log Q) ≤ c₃ * L := by rwa [div_le_iff₀ hc₃, mul_comm L] at hL3
      have h2 : c₃ * (L ^ 2 / 8) ≤ c₃ * u / lm := by
        rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_left hP2 hc₃.le
      have h9 := mul_le_mul_of_nonneg_right this hL0.le
      have : Real.log Q ≤ Real.log Q * L := by nlinarith
      have e : c₃ * (L ^ 2 / 8) = c₃ * L * L / 8 := by ring
      linarith
    have t2 : B * L + Real.log Q ≤ Real.sqrt (c₃ * u) := by
      have : (B + 1) * L ≤ Real.sqrt (c₃ * u) := by
        apply Real.le_sqrt_of_sq_le
        have : c₃ * ((B + 1) ^ 2 / c₃ * L ^ 3) = (B + 1) ^ 2 * L ^ 3 := by field_simp
        have h3 : (B + 1) ^ 2 / c₃ * L ^ 3 ≤ u := by
          linarith
        have := mul_le_mul_of_nonneg_left h3 hc₃.le
        have hL23 : L ^ 2 ≤ L ^ 3 := by
          have : L ^ 3 = L ^ 2 * L := by ring
          rw [this]; nlinarith [sq_nonneg L]
        have e : ((B + 1) * L) ^ 2 = (B + 1) ^ 2 * L ^ 2 := by ring
        have := mul_le_mul_of_nonneg_left hL23 (sq_nonneg (B + 1))
        rw [e]; linarith
      linarith
    have := key _ t1
    have := key _ t2
    linarith
  · have hl4 : Real.log 4 ≤ 2 := by
      have e : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
      have := Real.log_two_lt_d9; linarith
    have h4L : 4 * L ≤ L ^ 3 := by
      have : L ^ 3 = L ^ 2 * L := by ring
      rw [this]; nlinarith
    have h5L := mul_le_mul_of_nonneg_left h4L (by linarith : 0 ≤ B + 1)
    have h6L : 0 ≤ B * L := by positivity
    calc Real.exp (-(2 / 5 * u)) ≤ Real.exp (-(B * L) - Real.log 4) := Real.exp_le_exp.mpr (by linarith)
      _ = _ := by rw [Real.exp_sub, Real.exp_log (by norm_num)]

set_option maxHeartbeats 1000000 in
theorem twistK :
    ∀ ε A B : ℝ, 0 < ε → 0 < A → 0 < B → ∃ Y₀ : ℝ, ∀ Y ≥ Y₀, ∀ (U : ℝ) (m₀ a₀ : ℕ), admitted ε Y U m₀ a₀ →
      ∃ nstar : ℕ, ∀ s : ℕ, 1 < s → Odd s → Squarefree s → s.Coprime m₀ → (s : ℝ) ≤ Y ^ A → s ≠ nstar →
        |∑ q ∈ PPset m₀ a₀ U, (jacobiSym (q : ℤ) s : ℝ)| ≤ Y ^ (-B) * ((PPset m₀ a₀ U).card : ℝ) := by
  classical
  intro ε A B hε hA0 hB0
  have hP : PNTAPRelW := Formalism.HermitianLattices.Ext.PrimesInProgressions.pnt_progressions_relative_weak_holds
  have hZ : Formalism.ZeroFreeDirichlet.ZFRDirichlet := Formalism.ZeroFreeDirichlet.zFRDirichlet
  have hE : Formalism.ZeroFreeDirichlet.ExcBound := Formalism.ZeroFreeDirichlet.excBound
  obtain ⟨x₁, hx₁⟩ := count_a hP hE ε hε
  obtain ⟨c₀, hc₀, hpage⟩ := page_across hZ
  obtain ⟨c₃, A₀, C₀, hc₃, H⟩ := hP
  have H' : ∀ M : ℕ, ∃ e : Option (DirichletCharacter ℂ M × ℝ), ∀ (hM : 0 < M), 8 ∣ M →
      (∀ p : DirichletCharacter ℂ M × ℝ, e = some p → @IsExcPair M ⟨hM.ne'⟩ p.1 p.2) ∧
      ∀ (X : ℝ) (b : ℕ), 2 ≤ X → C₀ * Real.log M * Real.log (Real.log M + 2) ≤ Real.log X → b.Coprime M →
        |(piAP X M b : ℝ) - mainAP e b X| ≤
          A₀ * (Real.exp (-(c₃ * Real.log X / Real.log M)) + Real.exp (-Real.sqrt (c₃ * Real.log X))) *
            mainAP e b X := by
    intro M
    by_cases h : 0 < M ∧ 8 ∣ M
    · obtain ⟨e, he1, _, he3⟩ := @H M ⟨h.1.ne'⟩ h.2
      exact ⟨e, fun _ _ => ⟨he1, he3⟩⟩
    · exact ⟨none, fun hM h8 => absurd ⟨hM, h8⟩ h⟩
  choose E hE using H'
  obtain ⟨x₂, hx₂⟩ := eventually_log_cube (A / 4 + (B + 1) ^ 2 / c₃ + 5 * (B + 1)) (ε / 6) (by positivity) (by positivity)
  set L₀ : ℝ := max (max 2 (8 * (ε / 5 + 2 + B + Real.log 128) / c₀))
    (max (max (8 * (B + Real.log (32 * (|A₀| + 1))) / c₃) (Real.log (32 * (|A₀| + 1))))
      (8 * |C₀| * (Real.log (6 + A) + ε / 5 + 1))) with hL₀
  refine ⟨max (max x₁ x₂) (Real.exp L₀), ?_⟩
  intro x hx X m₀ a₀ ⟨hm, h8, ha, hX1, hX2, hX3⟩
  have hxx₁ : x₁ ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hxx₂ : x₂ ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hxL : Real.exp L₀ ≤ x := le_trans (le_max_right _ _) hx
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hxL
  have hLL : L₀ ≤ Real.log x := by rw [Real.le_log_iff_exp_le hx0]; exact hxL
  have hL1 : 2 ≤ Real.log x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hLL
  have hL2 : 8 * (ε / 5 + 2 + B + Real.log 128) / c₀ ≤ Real.log x :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hLL
  have hL3 : 8 * (B + Real.log (32 * (|A₀| + 1))) / c₃ ≤ Real.log x :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _)) hLL
  have hL4 : Real.log (32 * (|A₀| + 1)) ≤ Real.log x :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_right _ _)) hLL
  have hL5 : 8 * |C₀| * (Real.log (6 + A) + ε / 5 + 1) ≤ Real.log x :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hLL
  have hx1 : 1 ≤ x := by
    have := Real.add_one_le_exp (Real.log x)
    rw [Real.exp_log hx0] at this; linarith
  have hu2 : (A / 4 + (B + 1) ^ 2 / c₃ + 5 * (B + 1)) * Real.log x ^ 3 ≤ Real.log X := (hx₂ x hxx₂).trans hX2
  have hu0 : 0 < Real.log X := by
    have : 0 < (A / 4 + (B + 1) ^ 2 / c₃ + 5 * (B + 1)) * Real.log x ^ 3 := by positivity
    linarith
  rcases le_or_gt X 0 with hXn | hXp
  · refine ⟨0, fun s _ _ _ _ _ _ => ?_⟩
    have : PPset m₀ a₀ X = ∅ := by
      unfold PPset; rw [Nat.floor_of_nonpos hXn]; simp
    simp [this]

  have hm8 : 8 ≤ m₀ := Nat.le_of_dvd hm h8
  have hl2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlog8 : 2 ≤ Real.log 8 := by
    have : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
    linarith
  have hX4 : 4 ≤ X := by
    have h4 : Real.log 4 ≤ Real.log X := by
      have : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
      have := Real.log_two_lt_d9
      have : (8 : ℝ) ≤ Real.log x ^ 3 := by nlinarith
      have hK : 5 ≤ (A / 4 + (B + 1) ^ 2 / c₃ + 5 * (B + 1)) := by
        have : 0 ≤ (B + 1) ^ 2 / c₃ := by positivity
        linarith
      have := mul_le_mul_of_nonneg_right hK (by linarith : 0 ≤ Real.log x ^ 3)
      linarith
    exact (Real.log_le_log_iff (by norm_num) hXp).mp h4
  have hxA : 1 ≤ x ^ A := Real.one_le_rpow hx1 hA0.le
  have hm0 : (0 : ℝ) < m₀ := by exact_mod_cast hm
  obtain ⟨Z, hZdef⟩ : ∃ Z : ℝ, Z = (m₀ : ℝ) * x ^ A := ⟨_, rfl⟩
  have hZ3 : 3 ≤ Z := by
    have : (8 : ℝ) ≤ m₀ := by exact_mod_cast hm8
    rw [hZdef]; nlinarith
  have hℓ : Real.log Z ≤ Real.log m₀ + A * Real.log x := by
    rw [hZdef, Real.log_mul hm0.ne' (by positivity), Real.log_rpow hx0]
  have hℓm : Real.log m₀ ≤ 4 * Real.exp (ε / 5 * Real.log x) := by
    have hxe : x ^ (ε / 5) = Real.exp (ε / 5 * Real.log x) := by
      rw [Real.rpow_def_of_pos hx0, mul_comm]
    have hLp : 0 < Real.log x ^ 2 := by positivity
    have h := hX1.trans hX3
    rw [hxe] at h
    have : Real.log m₀ / 4 * Real.log x ^ 2 ≤ Real.exp (ε / 5 * Real.log x) * Real.log x ^ 2 := by linarith
    have := le_of_mul_le_mul_right this hLp
    linarith
  have hlogu : Real.log (Real.log X) ≤ (ε / 5 + 2) * Real.log x := by
    have hLp : 0 < Real.log x := by linarith
    calc Real.log (Real.log X) ≤ Real.log (x ^ (ε / 5) * Real.log x ^ 2) := Real.log_le_log hu0 hX3
      _ = ε / 5 * Real.log x + 2 * Real.log (Real.log x) := by
          rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow hx0, Real.log_pow]; push_cast; ring
      _ ≤ _ := by
          have := Real.log_le_sub_one_of_pos hLp
          nlinarith

  let bad : ℕ → Prop := fun s => 1 < s ∧ Odd s ∧ Squarefree s ∧ s.Coprime m₀ ∧ (s : ℝ) ≤ x ^ A ∧
      ∃ (χ : DirichletCharacter ℂ (m₀ * s)) (β : ℝ), E (m₀ * s) = some (χ, β) ∧ 1 - β < c₀ / Real.log Z ∧
        ∀ u : ℕ, u % m₀ = 1 % m₀ → u.Coprime s → χ (u : ZMod (m₀ * s)) = ((jacobiSym (u : ℤ) s : ℤ) : ℂ)
  have hMZ : ∀ t : ℕ, (t : ℝ) ≤ x ^ A → ((m₀ * t : ℕ) : ℝ) ≤ Z := fun t ht => by
    rw [hZdef]; push_cast; exact mul_le_mul_of_nonneg_left ht hm0.le
  have huniq : ∀ s₁ s₂, bad s₁ → bad s₂ → s₁ = s₂ := by
    rintro s₁ s₂ ⟨h11, ho1, hq1, hc1, hN1', χ₁, β₁, he1, hlt1, hal1⟩ ⟨h12, ho2, hq2, hc2, hN2', χ₂, β₂, he2, hlt2, hal2⟩
    have hM1 : 0 < m₀ * s₁ := Nat.mul_pos hm (by omega)
    have hM2 : 0 < m₀ * s₂ := Nat.mul_pos hm (by omega)
    have : NeZero (m₀ * s₁) := ⟨hM1.ne'⟩
    have : NeZero (m₀ * s₂) := ⟨hM2.ne'⟩
    obtain ⟨sq1, ne1, L1, _, lt1⟩ := (hE (m₀ * s₁) hM1 (dvd_mul_of_dvd_left h8 _)).1 _ he1
    obtain ⟨sq2, ne2, L2, _, lt2⟩ := (hE (m₀ * s₂) hM2 (dvd_mul_of_dvd_left h8 _)).1 _ he2
    have hag := hpage Z (m₀ * s₁) (m₀ * s₂) χ₁ χ₂ β₁ β₂ hZ3 (hMZ _ hN1') (hMZ _ hN2') sq1 sq2 ne1 ne2 L1 L2
      (by linarith) (by linarith) lt1 lt2
    apply jacobi_separate m₀ s₁ s₂ hm ho1 ho2 hq1 hq2 hc1 hc2
    intro u hu hus
    have hum : u.Coprime m₀ := by
      unfold Nat.Coprime; rw [Nat.ModEq.gcd_eq (show u ≡ 1 [MOD m₀] from hu)]; simp
    have hu1 : u.Coprime s₁ := (Nat.coprime_mul_iff_right.mp hus).1
    have hu2' : u.Coprime s₂ := (Nat.coprime_mul_iff_right.mp hus).2
    have hn : u.Coprime ((m₀ * s₁) * (m₀ * s₂)) :=
      Nat.Coprime.mul_right (Nat.Coprime.mul_right hum hu1) (Nat.Coprime.mul_right hum hu2')
    have := hag u hn
    rw [hal1 u hu hu1, hal2 u hu hu2'] at this
    exact_mod_cast this
  refine ⟨if h : ∃ s, bad s then Classical.choose h else 0, ?_⟩
  intro s h1 hodd hsq hcop hsN hne
  have hnb : ¬ bad s := by
    intro hb
    have hex : ∃ s, bad s := ⟨s, hb⟩
    rw [dif_pos hex] at hne
    exact hne (huniq _ _ hb (Classical.choose_spec hex))
  have hM : 0 < m₀ * s := Nat.mul_pos hm (by omega)
  have h8M : 8 ∣ m₀ * s := dvd_mul_of_dvd_left h8 s
  have : NeZero (m₀ * s) := ⟨hM.ne'⟩
  obtain ⟨hEx, hPNT⟩ := hE (m₀ * s) hM h8M
  have hlm0 : 2 ≤ Real.log ((m₀ * s : ℕ) : ℝ) := by
    have : (8 : ℝ) ≤ ((m₀ * s : ℕ) : ℝ) := by
      exact_mod_cast le_trans hm8 (Nat.le_mul_of_pos_right _ (by omega))
    linarith [Real.log_le_log (by norm_num) this]
  have hlm : Real.log ((m₀ * s : ℕ) : ℝ) ≤ Real.log Z :=
    Real.log_le_log (by exact_mod_cast hM) (hMZ s hsN)
  obtain ⟨f1, f2, f3, f4⟩ := final_ineqK A B ε c₀ c₃ A₀ C₀ (Real.log x) (Real.log X) (Real.log ((m₀ * s : ℕ) : ℝ))
    (Real.log m₀) (Real.log Z) hA0 hB0 hε hc₀ hc₃ hL1 hL2 hL3 hL4 hL5 hX1 hu2 hlogu hℓm hlm0 hlm hℓ
  set η : ℝ := Real.exp (-(B * Real.log x)) with hη
  have hη1 : η ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hη0 : 0 ≤ η := (Real.exp_pos _).le
  have hxη : x ^ (-B) = η := by rw [Real.rpow_def_of_pos hx0, hη]; ring_nf
  set ρ : ℝ := Real.exp (-(c₃ * Real.log X / Real.log ((m₀ * s : ℕ) : ℝ))) +
    Real.exp (-Real.sqrt (c₃ * Real.log X)) with hρ
  have hρ0 : 0 < ρ := by positivity
  set k : ℝ := A₀ * ρ with hk
  have hkabs : |k| = |A₀| * ρ := by rw [hk, abs_mul, abs_of_pos hρ0]
  have hk2 : 2 * |k| ≤ η / 8 := by rw [hkabs, ← mul_assoc]; exact f3
  have hk' : |k| ≤ 1 / 2 := by linarith
  set r : ℝ := 4 * Real.log X * Real.exp (-(c₀ / Real.log Z * Real.log X)) with hr
  have hr0 : 0 ≤ r := by positivity
  have hr4 : 4 * r ≤ η / 8 := by
    have : 4 * r = 16 * Real.log X * Real.exp (-(c₀ / Real.log Z * Real.log X)) := by rw [hr]; ring
    rw [this]; exact f2
  have hr' : r ≤ 1 / 2 := by linarith
  have hli : 0 < liX X := lt_of_lt_of_le (by positivity) (liX_lower hX4)
  have hb : ∀ b ∈ clsB m₀ s a₀, |(piAP X (m₀ * s) b : ℝ) - mainAP (E (m₀ * s)) b X| ≤
      k * mainAP (E (m₀ * s)) b X :=
    fun b hbB => hPNT X b (by linarith) f1 (coprime_of_cls ha hbB)
  have hG : ∀ (χ : DirichletCharacter ℂ (m₀ * s)) (β : ℝ), E (m₀ * s) = some (χ, β) →
      (∀ u : ℕ, u % m₀ = 1 % m₀ → u.Coprime s → χ (u : ZMod (m₀ * s)) = ((jacobiSym (u : ℤ) s : ℤ) : ℂ)) →
      |liX (X ^ β)| ≤ r * liX X := by
    intro χ β heq hal
    obtain ⟨_, _, _, hβl, _⟩ := hEx (χ, β) heq
    have hβ2 : β ≤ 1 - c₀ / Real.log Z := by
      by_contra hc
      exact hnb ⟨h1, hodd, hsq, hcop, hsN, χ, β, heq, by linarith, hal⟩
    have hβ1 : 1 / 2 ≤ β := by
      have : 1 / (8 * Real.log ((m₀ * s : ℕ) : ℝ)) ≤ 1 / 2 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
      simp only at hβl
      linarith
    exact liX_pow_le hX4 hβ1 hβ2
  have hmain := twist_one m₀ s a₀ hm h1 hodd hsq hcop.symm ha X r k (E (m₀ * s)) hXp.le hr0 hr' hli hk' hb hG
  have hcount := hx₁ x X m₀ a₀ hxx₁ hm h8 ha hX1 hX2 hX3
  set P : ℝ := ((PPset m₀ a₀ X).card : ℝ)
  set d : ℝ := Real.exp (-(2 / 5 * Real.log X))
  have hsq2 : X ^ (1 / 2 : ℝ) ≤ d * P := by
    have e : X ^ (1 / 2 : ℝ) = X ^ (-(2 / 5) : ℝ) * X ^ (9 / 10 : ℝ) := by
      rw [← Real.rpow_add hXp]; norm_num
    have e2 : X ^ (-(2 / 5) : ℝ) = d := by
      rw [Real.rpow_def_of_pos hXp]; show _ = Real.exp _; congr 1; ring
    rw [e, e2]
    exact mul_le_mul_of_nonneg_left hcount (Real.exp_pos _).le
  have hP0 : 0 ≤ P := Nat.cast_nonneg _
  have hd0 : 0 ≤ d := (Real.exp_pos _).le
  have ha4 : 4 * r + 2 * |k| ≤ η / 4 := by linarith
  have t1 : (4 * r + 2 * |k|) * (P + X ^ (1 / 2 : ℝ)) ≤ η / 4 * (P + d * P) :=
    mul_le_mul ha4 (by linarith) (add_nonneg hP0 (Real.rpow_nonneg hXp.le _)) (by linarith)
  have t2 : d * P ≤ η / 4 * P := mul_le_mul_of_nonneg_right f4 hP0
  have t3 : η / 4 * (d * P) ≤ η / 4 * (1 / 4 * P) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by linarith) hP0) (by linarith)
  rw [hxη]
  have : η / 4 * (P + d * P) = η / 4 * P + η / 4 * (d * P) := by ring
  have hηP : 0 ≤ η * P := mul_nonneg hη0 hP0
  have e3 : η / 4 * (1 / 4 * P) = η * P / 16 := by ring
  have e4 : η / 4 * P = η * P / 4 := by ring
  linarith

end QH
