import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.StripEstimates.FaceMapCompSuccAboveCastSucc

noncomputable section

open UpperHalfPlane hiding I
open MeasureTheory Complex CongruenceSubgroup Filter Topology
open scoped MatrixGroups ModularForm Modular ComplexConjugate Real
open Ad3 Ad3.S

namespace GlobalTheory.CompanionTheory.ShimStep

theorem exp_mul_le {C₁ C₂ u : ℝ} (h₁ : 0 ≤ C₁) (h₂ : 0 ≤ C₂) (hu : 0 ≤ u) :
    (C₁ * Real.exp (C₁ * u)) * (C₂ * Real.exp (C₂ * u)) ≤
      (C₁ * C₂ + C₁ + C₂) * Real.exp ((C₁ * C₂ + C₁ + C₂) * u) := by
  have e : Real.exp (C₁ * u) * Real.exp (C₂ * u) = Real.exp ((C₁ + C₂) * u) := by
    rw [← Real.exp_add]; ring_nf
  have h12 := mul_nonneg h₁ h₂
  calc (C₁ * Real.exp (C₁ * u)) * (C₂ * Real.exp (C₂ * u))
      = (C₁ * C₂) * Real.exp ((C₁ + C₂) * u) := by rw [← e]; ring
    _ ≤ _ := by
      apply mul_le_mul (by linarith) _ (Real.exp_pos _).le (by positivity)
      apply Real.exp_le_exp.2
      apply mul_le_mul_of_nonneg_right _ hu
      linarith

theorem abs_exp_le (C u : ℝ) (hu : 0 ≤ u) :
    C * Real.exp (C * u) ≤ |C| * Real.exp (|C| * u) := by
  apply mul_le_mul (le_abs_self C) _ (Real.exp_pos _).le (abs_nonneg C)
  exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (le_abs_self C) hu)

theorem integral_holo (hHI : HI) {X : Type} [MeasurableSpace X] (m : Measure X) (F : ℂ → X → ℂ)
    (hmeas : ∀ s ∈ HP (1 / 4), AEStronglyMeasurable (F s) m)
    (hdiff : ∀ x, DifferentiableOn ℂ (fun s => F s x) (HP (1 / 4)))
    (hbound : ∀ b : ℝ, ∃ (C : ℝ) (g : X → ℝ), 0 ≤ C ∧ Integrable g m ∧ (∀ x, 0 ≤ g x) ∧
      ∀ s x, 1 / 4 < s.re → s.re ≤ b → ‖F s x‖ ≤ C * Real.exp (C * s.im ^ 2) * g x) :
    DifferentiableOn ℂ (fun s => ∫ x, F s x ∂m) (HP (1 / 4)) ∧
    ∀ b : ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, 1 / 4 < s.re → s.re ≤ b →
      ‖∫ x, F s x ∂m‖ ≤ C * Real.exp (C * s.im ^ 2) := by
  constructor
  · have hop : IsOpen (HP (1 / 4)) := isOpen_lt continuous_const continuous_re
    refine hHI X m (HP (1 / 4)) F hop hmeas hdiff ?_
    intro s₀ hs₀
    obtain ⟨C, g, hC, hg, hg0, hb⟩ := hbound (s₀.re + 1)
    refine ⟨fun x => (C * Real.exp (C * (|s₀.im| + 1) ^ 2)) * g x, hg.const_mul _, ?_⟩
    have h1 : ∀ᶠ s in 𝓝 s₀, s ∈ HP (1 / 4) := hop.mem_nhds hs₀
    have h2 : ∀ᶠ s : ℂ in 𝓝 s₀, s.re < s₀.re + 1 :=
      (continuous_re.tendsto s₀).eventually (gt_mem_nhds (by linarith))
    have h3 : ∀ᶠ s : ℂ in 𝓝 s₀, |s.im| < |s₀.im| + 1 :=
      ((continuous_abs.comp Complex.continuous_im).tendsto s₀).eventually (gt_mem_nhds (by simp))
    filter_upwards [h1, h2, h3] with s a1 a2 a3 x
    refine (hb s x a1 a2.le).trans ?_
    have hq : s.im ^ 2 ≤ (|s₀.im| + 1) ^ 2 := by
      rw [← sq_abs s.im]
      exact pow_le_pow_left₀ (abs_nonneg _) a3.le 2
    have := hg0 x
    gcongr
  · intro b
    obtain ⟨C, g, hC, hg, hg0, hb⟩ := hbound b
    have hI : 0 ≤ ∫ x, g x ∂m := integral_nonneg hg0
    refine ⟨C + C * ∫ x, g x ∂m, by positivity, fun s h1 h2 => ?_⟩
    have hE : ‖∫ x, F s x ∂m‖ ≤ ∫ x, C * Real.exp (C * s.im ^ 2) * g x ∂m :=
      norm_integral_le_of_norm_le (hg.const_mul _)
        (Filter.Eventually.of_forall fun x => hb s x h1 h2)
    rw [integral_const_mul] at hE
    refine hE.trans ?_
    have hCI := mul_nonneg hC hI
    have hu := sq_nonneg s.im
    have e1 : Real.exp (C * s.im ^ 2) ≤ Real.exp ((C + C * ∫ x, g x ∂m) * s.im ^ 2) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (by linarith) hu)
    calc C * Real.exp (C * s.im ^ 2) * ∫ x, g x ∂m
        = (C * ∫ x, g x ∂m) * Real.exp (C * s.im ^ 2) := by ring
      _ ≤ (C + C * ∫ x, g x ∂m) * Real.exp ((C + C * ∫ x, g x ∂m) * s.im ^ 2) :=
        mul_le_mul (by linarith) e1 (Real.exp_pos _).le (by linarith)

def fac (k ν : ℕ) (s : ℂ) : ℂ :=
  (1 / 2) * (Gamma (om k ν s - 1))⁻¹ * (4 * π : ℂ) ^ (om k ν s - 1)

theorem four_pi_ne : (4 * π : ℂ) ≠ 0 := by
  have := Real.pi_pos
  exact_mod_cast (by positivity : (4 * π : ℝ) ≠ 0)

theorem fac_differentiable (k ν : ℕ) : Differentiable ℂ (fac k ν) := by
  have hw : Differentiable ℂ fun s : ℂ => om k ν s - 1 := by
    unfold om; fun_prop
  have h1 : Differentiable ℂ fun s : ℂ => (Gamma (om k ν s - 1))⁻¹ :=
    differentiable_one_div_Gamma.comp hw
  have h2 : Differentiable ℂ fun s : ℂ => (4 * π : ℂ) ^ (om k ν s - 1) :=
    hw.const_cpow (Or.inl four_pi_ne)
  unfold fac
  exact (h1.const_mul _).mul h2

theorem fac_bound (hG : G0) (k ν : ℕ) (b : ℝ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, 1 / 4 < s.re → s.re ≤ b →
    ‖fac k ν s‖ ≤ C * Real.exp (C * s.im ^ 2) := by
  obtain ⟨C₀, h₀⟩ := hG (-1) ((b + k + ν + 1) / 2)
  have hpi := Real.pi_gt_three
  set B : ℝ := (b + k + ν + 1) / 2 with hB
  set K : ℝ := (4 * π) ^ B with hK
  have hK0 : 0 < K := Real.rpow_pos_of_pos (by positivity) _
  refine ⟨|C₀| * (1 + K), by positivity, fun s h1 h2 => ?_⟩
  have hre : (om k ν s - 1).re = (s.re + k + ν + 1) / 2 - 1 := by
    simp [om]
  have him : (om k ν s - 1).im = s.im / 2 := by
    simp [om]
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hν0 : (0 : ℝ) ≤ ν := Nat.cast_nonneg ν
  have g1 := h₀ (om k ν s - 1) (by rw [hre]; linarith) (by rw [hre, hB]; linarith)
  rw [him] at g1
  have g2 : ‖(4 * π : ℂ) ^ (om k ν s - 1)‖ ≤ K := by
    have : (4 * π : ℂ) = ((4 * π : ℝ) : ℂ) := by push_cast; ring
    rw [this, norm_cpow_eq_rpow_re_of_pos (by positivity), hre]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by rw [hB]; linarith)
  have hu := sq_nonneg s.im
  have g3 : C₀ * Real.exp (C₀ * (s.im / 2) ^ 2) ≤ |C₀| * Real.exp (|C₀| * s.im ^ 2) := by
    apply mul_le_mul (le_abs_self C₀) _ (Real.exp_pos _).le (abs_nonneg C₀)
    apply Real.exp_le_exp.2
    have := le_abs_self C₀
    have h0 := abs_nonneg C₀
    nlinarith [mul_nonneg h0 hu]
  have g4 : |C₀| * Real.exp (|C₀| * s.im ^ 2) * K ≤
      |C₀| * (1 + K) * Real.exp (|C₀| * (1 + K) * s.im ^ 2) := by
    have h0 := abs_nonneg C₀
    have e : Real.exp (|C₀| * s.im ^ 2) ≤ Real.exp (|C₀| * (1 + K) * s.im ^ 2) := by
      apply Real.exp_le_exp.2
      apply mul_le_mul_of_nonneg_right _ hu
      nlinarith
    calc |C₀| * Real.exp (|C₀| * s.im ^ 2) * K = (|C₀| * K) * Real.exp (|C₀| * s.im ^ 2) := by ring
      _ ≤ _ := mul_le_mul (by nlinarith) e (Real.exp_pos _).le (by positivity)
  unfold fac
  rw [norm_mul, norm_mul]
  have n2 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
  rw [n2]
  have hpos : 0 ≤ |C₀| * Real.exp (|C₀| * s.im ^ 2) := by positivity
  calc 1 / 2 * ‖(Gamma (om k ν s - 1))⁻¹‖ * ‖(4 * π : ℂ) ^ (om k ν s - 1)‖
      ≤ 1 * (|C₀| * Real.exp (|C₀| * s.im ^ 2)) * K := by
        apply mul_le_mul _ g2 (norm_nonneg _) (by positivity)
        have := g1.trans g3
        have h3 := norm_nonneg (Gamma (om k ν s - 1))⁻¹
        linarith
    _ ≤ _ := by rw [one_mul]; exact g4

theorem th_le {C : ℝ} {ν : ℕ} (hν : ν ≤ 1) {z : ℍ} (h1 : 1 ≤ Ht z) (h2 : z.im⁻¹ ≤ Ht z)
    {x : ℝ} (hx : x ≤ C * z.im ^ (-((ν : ℝ) + 1) / 2)) : x ≤ |C| * Ht z := by
  have hy := z.im_pos
  have hp : z.im ^ (-((ν : ℝ) + 1) / 2) ≤ Ht z := by
    have hν' : (ν : ℝ) ≤ 1 := by exact_mod_cast hν
    have hν0 : (0 : ℝ) ≤ ν := Nat.cast_nonneg ν
    have e : -((ν : ℝ) + 1) / 2 = -(((ν : ℝ) + 1) / 2) := by ring
    rw [e, Real.rpow_neg hy.le, ← Real.inv_rpow hy.le]
    calc z.im⁻¹ ^ (((ν : ℝ) + 1) / 2) ≤ Ht z ^ (((ν : ℝ) + 1) / 2) :=
          Real.rpow_le_rpow (by positivity) h2 (by positivity)
      _ ≤ Ht z ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
      _ = Ht z := Real.rpow_one _
  have hp0 : 0 ≤ z.im ^ (-((ν : ℝ) + 1) / 2) := Real.rpow_nonneg hy.le _
  calc x ≤ C * z.im ^ (-((ν : ℝ) + 1) / 2) := hx
    _ ≤ |C| * z.im ^ (-((ν : ℝ) + 1) / 2) := mul_le_mul_of_nonneg_right (le_abs_self C) hp0
    _ ≤ |C| * Ht z := mul_le_mul_of_nonneg_left hp (abs_nonneg C)

theorem integrand_bound (hPR : PR) (L k ν : ℕ) (hL : 0 < L) (hν : ν ≤ 1) (β : ℍ → ℝ)
    (hβ : ∀ z, 0 ≤ β z ∧ β z ≤ 1) (U : Set ℍ) (hU : ∀ z, β z ≠ 0 → z ∈ U) (f t : ℍ → ℂ)
    (Es : ℂ → ℂ → ℂ) (hth : ∃ C : ℝ, ∀ z : ℍ, ‖t z‖ ≤ C * z.im ^ (-((ν : ℝ) + 1) / 2))
    (hEs : ∀ b : ℝ, ∃ (C : ℝ) (A : ℕ), ∀ s v : ℂ, 1 / 4 < s.re → s.re ≤ b → 0 < v.im →
      ‖Es s v‖ ≤ C * Real.exp (C * s.im ^ 2) * (v.im ^ A + v.im⁻¹ ^ A)) (b : ℝ) :
    ∃ (C : ℝ) (A : ℕ), 0 ≤ C ∧ ∀ (s : ℂ) (z : ℍ), 1 / 4 < s.re → s.re ≤ b →
      ‖(β z : ℂ) * (f z * conj (t z) * pref L k ν s z * Es s (-1 / (z : ℂ) / (L : ℂ)))‖ ≤
        C * Real.exp (C * s.im ^ 2) * U.indicator (fun z => ‖f z‖ * Ht z ^ A) z := by
  obtain ⟨-, -, hp, hh⟩ := hPR L k ν hL
  obtain ⟨C₁, h₁⟩ := hth
  obtain ⟨C₂, A₂, h₂⟩ := hp b
  obtain ⟨C₃, A₃, h₃⟩ := hEs b
  set D : ℝ := |C₁| with hD
  set P : ℝ := |C₂| with hP
  set Q : ℝ := |C₃| * (1 + (L : ℝ) ^ A₃) with hQ
  have hD0 : 0 ≤ D := abs_nonneg _
  have hP0 : 0 ≤ P := abs_nonneg _
  have hQ0 : 0 ≤ Q := by positivity
  set R : ℝ := P * Q + P + Q with hR
  have hR0 : 0 ≤ R := by positivity
  refine ⟨D * R + R, 1 + A₂ + A₃, by positivity, fun s z hs hb => ?_⟩
  have hu := sq_nonneg s.im
  by_cases hz : β z = 0
  · have : 0 ≤ U.indicator (fun z => ‖f z‖ * Ht z ^ (1 + A₂ + A₃)) z := by
      apply Set.indicator_nonneg
      intro w _
      have := (hh w).1
      positivity
    simp only [hz, Complex.ofReal_zero, zero_mul, norm_zero]
    positivity
  rw [Set.indicator_of_mem (hU z hz)]
  obtain ⟨g1, g2, g3, g4, g5⟩ := hh z
  have hH0 : 0 ≤ Ht z := by linarith
  have b1 : ‖t z‖ ≤ D * Ht z := th_le hν g1 g2 (h₁ z)
  have b2 : ‖pref L k ν s z‖ ≤ P * Real.exp (P * s.im ^ 2) * Ht z ^ A₂ :=
    (h₂ s z (by linarith) hb).trans
      (mul_le_mul_of_nonneg_right (abs_exp_le _ _ hu) (by positivity))
  have b3 : ‖Es s (-1 / (z : ℂ) / (L : ℂ))‖ ≤ Q * Real.exp (Q * s.im ^ 2) * Ht z ^ A₃ := by
    refine (h₃ s _ hs hb g3).trans ?_
    have c1 : (-1 / (z : ℂ) / (L : ℂ)).im ^ A₃ ≤ Ht z ^ A₃ := pow_le_pow_left₀ g3.le g4 _
    have c2 : (-1 / (z : ℂ) / (L : ℂ)).im⁻¹ ^ A₃ ≤ (L : ℝ) ^ A₃ * Ht z ^ A₃ := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (inv_pos.2 g3).le g5 _
    have c3 : 0 ≤ (-1 / (z : ℂ) / (L : ℂ)).im ^ A₃ + (-1 / (z : ℂ) / (L : ℂ)).im⁻¹ ^ A₃ := by
      have := (inv_pos.2 g3).le
      have := g3.le
      positivity
    have hE : Real.exp (|C₃| * s.im ^ 2) ≤ Real.exp (Q * s.im ^ 2) := by
      apply Real.exp_le_exp.2
      apply mul_le_mul_of_nonneg_right _ hu
      have : 0 ≤ (L : ℝ) ^ A₃ := by positivity
      have h0 := abs_nonneg C₃
      rw [hQ]; nlinarith
    calc C₃ * Real.exp (C₃ * s.im ^ 2) * ((-1 / (z : ℂ) / (L : ℂ)).im ^ A₃ + (-1 / (z : ℂ) / (L : ℂ)).im⁻¹ ^ A₃)
        ≤ |C₃| * Real.exp (|C₃| * s.im ^ 2) * ((-1 / (z : ℂ) / (L : ℂ)).im ^ A₃ + (-1 / (z : ℂ) / (L : ℂ)).im⁻¹ ^ A₃) :=
          mul_le_mul_of_nonneg_right (abs_exp_le _ _ hu) c3
      _ ≤ |C₃| * Real.exp (|C₃| * s.im ^ 2) * (Ht z ^ A₃ + (L : ℝ) ^ A₃ * Ht z ^ A₃) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = Q * Real.exp (|C₃| * s.im ^ 2) * Ht z ^ A₃ := by rw [hQ]; ring
      _ ≤ Q * Real.exp (Q * s.im ^ 2) * Ht z ^ A₃ := by gcongr
  have bβ : ‖(β z : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hβ z).1]
    exact (hβ z).2
  have hm := exp_mul_le hP0 hQ0 hu
  have hHp : 0 ≤ Ht z ^ A₂ := by positivity
  have hHq : 0 ≤ Ht z ^ A₃ := by positivity
  have hf0 := norm_nonneg (f z)
  rw [norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_conj]
  have hE2 : 0 ≤ P * Real.exp (P * s.im ^ 2) * Ht z ^ A₂ := by positivity
  have hE3 : 0 ≤ Q * Real.exp (Q * s.im ^ 2) * Ht z ^ A₃ := by positivity
  have hfin : D * (R * Real.exp (R * s.im ^ 2)) ≤ (D * R + R) * Real.exp ((D * R + R) * s.im ^ 2) := by
    have e : Real.exp (R * s.im ^ 2) ≤ Real.exp ((D * R + R) * s.im ^ 2) := by
      apply Real.exp_le_exp.2
      apply mul_le_mul_of_nonneg_right _ hu
      nlinarith [mul_nonneg hD0 hR0]
    calc D * (R * Real.exp (R * s.im ^ 2)) = (D * R) * Real.exp (R * s.im ^ 2) := by ring
      _ ≤ _ := mul_le_mul (by linarith) e (Real.exp_pos _).le (by positivity)
  calc ‖(β z : ℂ)‖ * (‖f z‖ * ‖t z‖ * ‖pref L k ν s z‖ * ‖Es s (-1 / (z : ℂ) / (L : ℂ))‖)
      ≤ 1 * (‖f z‖ * (D * Ht z) * (P * Real.exp (P * s.im ^ 2) * Ht z ^ A₂) *
          (Q * Real.exp (Q * s.im ^ 2) * Ht z ^ A₃)) := by
        gcongr
    _ = D * ((P * Real.exp (P * s.im ^ 2)) * (Q * Real.exp (Q * s.im ^ 2))) *
          (‖f z‖ * Ht z ^ (1 + A₂ + A₃)) := by ring
    _ ≤ D * (R * Real.exp (R * s.im ^ 2)) * (‖f z‖ * Ht z ^ (1 + A₂ + A₃)) := by gcongr
    _ ≤ _ := mul_le_mul_of_nonneg_right hfin (by positivity)

theorem measurableSet_translate (σ : SL(2, ℤ)) : MeasurableSet {z : ℍ | σ⁻¹ • z ∈ 𝒟} := by
  have hc : Continuous fun z : ℍ => σ⁻¹ • z := by
    have : (fun z : ℍ => σ⁻¹ • z) = fun z : ℍ => (((σ⁻¹ : SL(2, ℤ)) : SL(2, ℝ)) : GL (Fin 2) ℝ) • z := rfl
    rw [this]
    exact continuous_const_smul _
  have hcl : IsClosed 𝒟 := by
    have h1 : IsClosed {z : ℍ | 1 ≤ normSq (z : ℂ)} :=
      isClosed_le continuous_const (Complex.continuous_normSq.comp UpperHalfPlane.continuous_coe)
    have h2 : IsClosed {z : ℍ | |z.re| ≤ 1 / 2} :=
      isClosed_le (continuous_abs.comp UpperHalfPlane.continuous_re) continuous_const
    exact h1.inter h2
  exact (hcl.preimage hc).measurableSet

theorem shim_of (h0 : U0) (hB2 : B2) (hD1 : D1) (hE0 : E0) (hPR : PR) (hG : G0) (hHI : HI)
    (hS : S1) : Shim := by
  intro k N M _ _ hM h4 hk χ f a hf c
  obtain ⟨ν, hν, hsign⟩ : ∃ ν : ℕ, ν ≤ 1 ∧
      (c * DirichletCharacter.changeLevel hM χ⁻¹) (-1) = (-1) ^ ν := by
    rcases (c * DirichletCharacter.changeLevel hM χ⁻¹).even_or_odd with h | h
    · exact ⟨0, by norm_num, by rw [pow_zero]; exact h⟩
    · exact ⟨1, le_rfl, by rw [pow_one]; exact h⟩
  have hMpos : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hL : 0 < 4 * M ^ 2 := by positivity
  obtain ⟨β, hβ, T, hT⟩ := h0 (4 * M ^ 2) hL
  obtain ⟨Es, e1, e2, e3, e4⟩ := hE0 M k ν (dvd_trans (by norm_num) h4) c
  obtain ⟨pr1, pr2, -, pr4⟩ := hPR (4 * M ^ 2) k ν hL
  have hM1 : 1 < M := by
    have := Nat.le_of_dvd hMpos h4
    omega
  have : Fact (1 < M) := ⟨hM1⟩
  have hP0 : (fun n : ℤ => (c * DirichletCharacter.changeLevel hM χ⁻¹)⁻¹ (n : ZMod M)) 0 = 0 := by
    show (c * DirichletCharacter.changeLevel hM χ⁻¹)⁻¹ ((0 : ℤ) : ZMod M) = 0
    rw [Int.cast_zero]
    exact MulChar.map_nonunit _ not_isUnit_zero
  have hP1 : ∀ n : ℤ, ‖(fun n : ℤ => (c * DirichletCharacter.changeLevel hM χ⁻¹)⁻¹ (n : ZMod M)) n‖ ≤ 1 :=
    fun n => DirichletCharacter.norm_le_one _ _
  obtain ⟨hcont, -, -, hthC⟩ := hB2 _ ν hν hP0 hP1
  set t : ℍ → ℂ := fun z => th (fun n : ℤ => (c * DirichletCharacter.changeLevel hM χ⁻¹)⁻¹ (n : ZMod M)) ν z with ht
  set U : Set ℍ := ⋃ σ ∈ T, {z : ℍ | σ⁻¹ • z ∈ 𝒟} with hUdef
  have hUm : MeasurableSet U := Finset.measurableSet_biUnion T fun σ _ => measurableSet_translate σ
  have hU : ∀ z, β z ≠ 0 → z ∈ U := by
    intro z hz
    obtain ⟨σ, hσ, h⟩ := hT z hz
    exact Set.mem_biUnion hσ h
  have hGint : ∀ A : ℕ, Integrable (U.indicator fun z => ‖f z‖ * Ht z ^ A) :=
    fun A => (integrable_indicator_iff hUm).2
      (integrableOn_finset_iUnion.2 fun σ _ => hD1 k N f σ A)
  have hHt : ∀ z, 0 ≤ Ht z := fun z => by
    have := (pr4 z).1
    linarith
  have hvim : ∀ z : ℍ, 0 < (-1 / (z : ℂ) / ((4 * M ^ 2 : ℕ) : ℂ)).im := fun z => (pr4 z).2.2.1
  let F : ℂ → ℍ → ℂ := fun s z => (β z : ℂ) * (f z * conj (t z) * pref (4 * M ^ 2) k ν s z *
    Es s (-1 / (z : ℂ) / ((4 * M ^ 2 : ℕ) : ℂ)))
  have hvm : Measurable fun z : ℍ => -1 / (z : ℂ) / ((4 * M ^ 2 : ℕ) : ℂ) :=
    (measurable_const.div UpperHalfPlane.continuous_coe.measurable).div_const _
  have hfm : Measurable (f : ℍ → ℂ) := (ModularFormClass.continuous f).measurable
  have hmeas : ∀ s ∈ HP (1 / 4), AEStronglyMeasurable (F s) volume := by
    intro s hs
    have hcj : Measurable fun z : ℍ => conj (t z) := (Complex.continuous_conj.comp hcont).measurable
    have hβc : Measurable fun z : ℍ => (β z : ℂ) := Complex.measurable_ofReal.comp hβ.1
    exact (hβc.mul (((hfm.mul hcj).mul (pr2 s)).mul ((e2 s hs).comp hvm))).aestronglyMeasurable
  have hdiff : ∀ z, DifferentiableOn ℂ (fun s => F s z) (HP (1 / 4)) := by
    intro z
    exact ((((pr1 z).differentiableOn).const_mul _).mul (e1 _ (hvim z))).const_mul _
  have hbound : ∀ b : ℝ, ∃ (C : ℝ) (g : ℍ → ℝ), 0 ≤ C ∧ Integrable g ∧ (∀ x, 0 ≤ g x) ∧
      ∀ s x, 1 / 4 < s.re → s.re ≤ b → ‖F s x‖ ≤ C * Real.exp (C * s.im ^ 2) * g x := by
    intro b
    obtain ⟨C, A, hC, h⟩ := integrand_bound hPR (4 * M ^ 2) k ν hL hν β hβ.2.1 U hU f t Es
      hthC e4 b
    refine ⟨C, _, hC, hGint A, fun z => ?_, h⟩
    apply Set.indicator_nonneg
    intro w _
    have := hHt w
    positivity
  obtain ⟨hcd, hcb⟩ := integral_holo hHI volume F hmeas hdiff hbound
  refine ⟨fun s => (∫ z, F s z) * fac k ν s, ?_, ?_, ?_⟩
  · exact hcd.mul (fac_differentiable k ν).differentiableOn
  · intro b
    obtain ⟨C₁, hC₁, g₁⟩ := hcb b
    obtain ⟨C₂, hC₂, g₂⟩ := fac_bound hG k ν b
    refine ⟨C₁ * C₂ + C₁ + C₂, fun s hs hb => ?_⟩
    have hs' : 1 / 4 < s.re := by linarith
    rw [norm_mul]
    exact (mul_le_mul (g₁ s hs' hb) (g₂ s hs' hb) (norm_nonneg _) (by positivity)).trans
      (exp_mul_le hC₁ hC₂ (sq_nonneg _))
  · intro s hs
    have hEq : ∀ z : ℍ, F s z = ((s - 1) * DirichletCharacter.LFunction (c ^ 2) (2 * s)) *
        ((β z : ℂ) * (f z * conj (th (fun n : ℤ => (c * DirichletCharacter.changeLevel hM χ⁻¹)⁻¹ (n : ZMod M)) ν z) *
          pref (4 * M ^ 2) k ν s z * Ep c k ν s (-1 / (z : ℂ) / ((4 * M ^ 2 : ℕ) : ℂ)))) := by
      intro z
      simp only [F]
      rw [e3 s _ hs (hvim z)]
      ring
    have hI : (∫ z, F s z) = ((s - 1) * DirichletCharacter.LFunction (c ^ 2) (2 * s)) *
        (2 * Gamma (om k ν s - 1) * (4 * π : ℂ) ^ (1 - om k ν s) *
          LSeries (fun n => (c * DirichletCharacter.changeLevel hM χ⁻¹) n * a (n ^ 2)) (s + k - 1)) := by
      simp only [hEq]
      rw [integral_const_mul, hS k N M ν hM h4 hk χ f a hf c hν hsign β hβ s hs]
    have hre : 0 < (om k ν s - 1).re := by
      have hk3 : (3 : ℝ) ≤ k := by exact_mod_cast hk
      have hν0 : (0 : ℝ) ≤ ν := Nat.cast_nonneg ν
      have : (om k ν s - 1).re = (s.re + k + ν + 1) / 2 - 1 := by simp [om]
      rw [this]; linarith
    have hΓ : Gamma (om k ν s - 1) * (Gamma (om k ν s - 1))⁻¹ = 1 :=
      mul_inv_cancel₀ (Complex.Gamma_ne_zero_of_re_pos hre)
    have hc : (4 * π : ℂ) ^ (1 - om k ν s) * (4 * π : ℂ) ^ (om k ν s - 1) = 1 := by
      rw [← cpow_add _ _ four_pi_ne]
      simp
    show (∫ z, F s z) * fac k ν s = _
    rw [hI]
    unfold fac
    linear_combination ((s - 1) * DirichletCharacter.LFunction (c ^ 2) (2 * s) *
        LSeries (fun n => (c * DirichletCharacter.changeLevel hM χ⁻¹) n * a (n ^ 2)) (s + k - 1) *
        (4 * π : ℂ) ^ (1 - om k ν s) * (4 * π : ℂ) ^ (om k ν s - 1)) * hΓ +
      ((s - 1) * DirichletCharacter.LFunction (c ^ 2) (2 * s) *
        LSeries (fun n => (c * DirichletCharacter.changeLevel hM χ⁻¹) n * a (n ^ 2)) (s + k - 1)) * hc

end GlobalTheory.CompanionTheory.ShimStep

end
