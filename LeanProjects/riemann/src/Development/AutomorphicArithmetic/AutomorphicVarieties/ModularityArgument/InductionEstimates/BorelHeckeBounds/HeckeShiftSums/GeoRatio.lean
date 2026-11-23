import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.Full
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.HeckeShiftSums.TriDiag
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.HeckeShiftSums.SgBasics
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.HpqMinor
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.HpSpec
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.PkLaws
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.QhtBasic

open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.K
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate

private theorem geo_div {d X B : ℝ} (hd : 1 ≤ d) (hB : 0 ≤ B) (h : d * X ≤ B) : X ≤ B := by
  by_contra hn
  push Not at hn
  nlinarith

private theorem geo_good {m h E ε c d H a₁ a₂ a₃ l : ℝ} (hm : 1 ≤ m) (hh : 0 < h) (hE : 0 ≤ E) (hε : 6 * m * ε = 1)
    (hcm : 12 * (m * c) ≤ 1) (hd : 1 ≤ d) (hl : 100 * (m * E) + 1 ≤ l)
    (h1 : |H - d * (a₁ / 2 + a₂ + a₃ / 2)| ≤ E) (h2 : l ≤ E + m * (|a₁| + |a₂| + |a₃|)) (h3 : H ≤ h * l + E)
    (h4 : -E ≤ a₁) (h5 : -E ≤ a₃) (hH : 0 < H) (h6 : a₁ + a₃ < ε * l) :
    c * l ≤ a₂ ∧ E < a₂ ∧ |a₁| + |a₂| + |a₃| ≤ (h + 2) * l := by
  obtain ⟨h1a, h1b⟩ := abs_le.1 h1
  have hmE : E ≤ m * E := by nlinarith
  have hl0 : 0 < l := by linarith
  have hε0 : 0 < ε := by
    by_contra hn
    push Not at hn
    nlinarith
  have hε1 : 6 * ε ≤ 1 := by nlinarith
  have hεl : 0 < ε * l := mul_pos hε0 hl0
  have hεl' : 6 * (ε * l) ≤ l := by nlinarith
  have hhl : 0 < h * l := mul_pos hh hl0
  have b1 : |a₁| ≤ ε * l + E := abs_le.2 ⟨by linarith, by linarith⟩
  have b3 : |a₃| ≤ ε * l + E := abs_le.2 ⟨by linarith, by linarith⟩
  have x1 : -(a₁ / 2 + a₂ + a₃ / 2) ≤ E := geo_div hd hE (by linarith)
  have x2 : a₁ / 2 + a₂ + a₃ / 2 ≤ h * l + 2 * E := geo_div hd (by linarith) (by linarith)
  have b2 : |a₂| ≤ a₂ + 2 * E + ε * l := abs_le.2 ⟨by linarith, by linarith⟩
  have s1 : m * (|a₁| + |a₂| + |a₃|) ≤ m * (a₂ + 4 * E + 3 * (ε * l)) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have e1 : m * (3 * (ε * l)) = l / 2 := by
    have : m * (3 * (ε * l)) = (6 * m * ε) * l / 2 := by ring
    rw [this, hε, one_mul]
  have s2 : l / 4 ≤ m * a₂ := by
    have : m * (a₂ + 4 * E + 3 * (ε * l)) = m * a₂ + 4 * (m * E) + m * (3 * (ε * l)) := by ring
    linarith
  have hm0 : 0 < m := by linarith
  have s3 : E < a₂ := lt_of_mul_lt_mul_left (by linarith : m * E < m * a₂) hm0.le
  refine ⟨le_of_mul_le_mul_left ?_ hm0, s3, ?_⟩
  · have : 12 * (m * c) * l ≤ 1 * l := mul_le_mul_of_nonneg_right hcm hl0.le
    have e : m * (c * l) = 12 * (m * c) * l / 12 := by ring
    linarith
  · rw [abs_of_nonneg (by linarith : 0 ≤ a₂)]
    have e : (h + 2) * l = h * l + 2 * l := by ring
    linarith

private theorem geo_bad {m h E ε c d H a₁ a₂ a₃ l : ℝ} (hm : 1 ≤ m) (hh : 0 < h) (hE : 0 ≤ E) (hc0 : 0 < c)
    (hc : 2 * c * (4 * h + 1) = ε) (hcm : 12 * (m * c) ≤ 1) (hd : 1 ≤ d) (hl : 100 * (m * E) + 1 ≤ l)
    (h1 : |H - d * (a₁ / 2 + a₂ + a₃ / 2)| ≤ E) (h2 : l ≤ E + m * (|a₁| + |a₂| + |a₃|)) (h3 : H ≤ h * l + E)
    (h4 : -E ≤ a₁) (h5 : -E ≤ a₃) (h6 : -E ≤ a₂) :
    c * l ≤ |a₁| + |a₂| + |a₃| ∧
      (a₁ < c * (|a₁| + |a₂| + |a₃|) → a₃ < c * (|a₁| + |a₂| + |a₃|) → E < a₂ ∧ a₁ + a₃ < ε * l) := by
  obtain ⟨h1a, h1b⟩ := abs_le.1 h1
  obtain ⟨r, hr⟩ : ∃ r, r = |a₁| + |a₂| + |a₃| := ⟨_, rfl⟩
  rw [← hr] at h2 ⊢
  have hmE : E ≤ m * E := by nlinarith
  have hl0 : 0 < l := by linarith
  have hm0 : 0 < m := by linarith
  have hhl : 0 < h * l := mul_pos hh hl0
  have s1 : 50 * E < r := lt_of_mul_lt_mul_left (by linarith : m * (50 * E) < m * r) hm0.le
  have hc1 : 12 * c ≤ 1 := by nlinarith
  have hcr : 12 * (c * r) ≤ r := by nlinarith
  have hcr0 : 0 ≤ c * r := mul_nonneg hc0.le (by linarith)
  refine ⟨le_of_mul_le_mul_left ?_ hm0, fun k1 k3 => ?_⟩
  · have : 12 * (m * c) * l ≤ 1 * l := mul_le_mul_of_nonneg_right hcm hl0.le
    have e : m * (c * l) = 12 * (m * c) * l / 12 := by ring
    linarith
  · have b1 : |a₁| ≤ c * r + E := abs_le.2 ⟨by linarith, by linarith⟩
    have b3 : |a₃| ≤ c * r + E := abs_le.2 ⟨by linarith, by linarith⟩
    have b2 : r / 2 ≤ a₂ := by
      rcases abs_cases a₂ with ⟨e, -⟩ | ⟨e, -⟩ <;> linarith
    have x2 : a₁ / 2 + a₂ + a₃ / 2 ≤ h * l + 2 * E := geo_div hd (by linarith) (by linarith)
    refine ⟨by linarith, ?_⟩
    have s2 : r ≤ (4 * h + 1) * l := by
      have e : (4 * h + 1) * l = 4 * (h * l) + l := by ring
      linarith
    have s3 : c * r ≤ c * ((4 * h + 1) * l) := mul_le_mul_of_nonneg_left s2 hc0.le
    have e : ε * l = 2 * (c * ((4 * h + 1) * l)) := by rw [← hc]; ring
    linarith

private theorem geo_ratio {ρ : Fin (2 + 2) → ℝ} (hρ : ∀ i, 0 < ρ i) (i j : Fin (2 + 2)) :
    ρ i / ρ j ≤ Real.exp (|Real.log (ρ 0 / ρ 1)| + |Real.log (ρ 1 / ρ 2)| + |Real.log (ρ 2 / ρ 3)|) := by
  rw [← Real.log_le_iff_le_exp (div_pos (hρ i) (hρ j))]
  simp only [Real.log_div (hρ _).ne' (hρ _).ne']
  have a1 := le_abs_self (Real.log (ρ 0) - Real.log (ρ 1))
  have a2 := le_abs_self (Real.log (ρ 1) - Real.log (ρ 2))
  have a3 := le_abs_self (Real.log (ρ 2) - Real.log (ρ 3))
  have b1 := neg_abs_le (Real.log (ρ 0) - Real.log (ρ 1))
  have b2 := neg_abs_le (Real.log (ρ 1) - Real.log (ρ 2))
  have b3 := neg_abs_le (Real.log (ρ 2) - Real.log (ρ 3))
  have c1 := abs_nonneg (Real.log (ρ 0) - Real.log (ρ 1))
  have c2 := abs_nonneg (Real.log (ρ 1) - Real.log (ρ 2))
  have c3 := abs_nonneg (Real.log (ρ 2) - Real.log (ρ 3))
  have hi : ∀ k : Fin (2 + 2), k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by decide
  rcases hi i with rfl | rfl | rfl | rfl <;> rcases hi j with rfl | rfl | rfl | rfl <;> linarith

private theorem geo_step {t E a b : ℝ} (ht : 0 < t) (ha : 0 < a) (hb : 0 < b) (hE : |Real.log t| ≤ E) :
    (t * b ≤ a → -E ≤ Real.log (a / b)) ∧ (E < Real.log (a / b) → t * b ≤ a) := by
  obtain ⟨h1, h2⟩ := abs_le.1 hE
  rw [← le_div_iff₀ hb, ← Real.log_le_log_iff ht (div_pos ha hb)]
  exact ⟨fun h => by linarith, fun h => by linarith⟩

private theorem geo_full {t : ℝ} {ρ : Fin (2 + 2) → ℝ} : Full t ρ ↔ Rel t ρ ∧ t * ρ 2 ≤ ρ 1 := by
  refine ⟨fun h => ⟨⟨h 0 1 rfl, h 2 3 rfl⟩, h 1 2 rfl⟩, fun ⟨⟨h1, h3⟩, h2⟩ i j hij => ?_⟩
  have hi : ∀ i j : Fin (2 + 2), (j : ℕ) = i + 1 → (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 3) := by decide
  rcases hi i j hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption

private theorem geo_logs {K : Type} [Field K] [NumberField K] (ω : Set (AdelicGLn.AdelicGL K (2 + 2))) (hω : Bor ω) :
    ∃ m h E : ℝ, 1 ≤ m ∧ 0 < h ∧ 0 ≤ E ∧ ∀ (ρ : Fin (2 + 2) → ℝ) (x : G1 K (2 + 2)), ∀ γ ∈ Gam K (2 + 2), Sg ω ρ (γ * x) →
      |HH (γ * x) - (Module.finrank ℚ K : ℝ) * (Real.log (ρ 0 / ρ 1) / 2 + Real.log (ρ 1 / ρ 2) + Real.log (ρ 2 / ρ 3) / 2)| ≤ E ∧
      Real.log (qht x) ≤ E + m * (|Real.log (ρ 0 / ρ 1)| + |Real.log (ρ 1 / ρ 2)| + |Real.log (ρ 2 / ρ 3)|) ∧
      HH (γ * x) ≤ h * Real.log (qht x) + E := by
  obtain ⟨C, c, hC, hs⟩ := sgBasics ω hω
  obtain ⟨h, D, hh, hD⟩ := hpQht (K := K)
  have hd : (0 : ℝ) ≤ (Module.finrank ℚ K : ℝ) := Nat.cast_nonneg _
  have hdC : 0 ≤ (Module.finrank ℚ K : ℝ) * C := mul_nonneg hd (by linarith)
  have hD0 := abs_nonneg D
  refine ⟨c + 1, h, C + (Module.finrank ℚ K : ℝ) * C + |D|, by linarith [Nat.cast_nonneg (α := ℝ) c], hh, by linarith,
    fun ρ x γ hγ hS => ?_⟩
  obtain ⟨s1, s2, s3⟩ := hs ρ _ hS
  have hρ : ∀ i, 0 < ρ i := hS.1
  refine ⟨?_, ?_, ?_⟩
  · rw [Real.log_mul (hρ _).ne' (hρ _).ne'] at s1
    rw [Real.log_mul (mul_pos (hρ _) (hρ _)).ne' (mul_pos (hρ _) (hρ _)).ne', Real.log_mul (hρ _).ne' (hρ _).ne',
      Real.log_mul (hρ _).ne' (hρ _).ne'] at s2
    simp only [Real.log_div (hρ _).ne' (hρ _).ne']
    obtain ⟨u1, u2⟩ := abs_le.1 s1
    obtain ⟨v1, v2⟩ := abs_le.1 s2
    have w1 := mul_le_mul_of_nonneg_left v1 hd
    have w2 := mul_le_mul_of_nonneg_left v2 hd
    refine abs_le.2 ⟨by linarith, by linarith⟩
  · obtain ⟨r, hr⟩ : ∃ r, r = |Real.log (ρ 0 / ρ 1)| + |Real.log (ρ 1 / ρ 2)| + |Real.log (ρ 2 / ρ 3)| := ⟨_, rfl⟩
    have hr0 : 0 ≤ r := by rw [hr]; positivity
    have u := s3 (Real.exp r) (Real.one_le_exp hr0) (fun i j => hr ▸ geo_ratio hρ i j)
    have v : qht x ≤ AutomorphicForm.height ((γ * x : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) :=
      ciInf_le (f := fun δ : Gam K (2 + 2) =>
        AutomorphicForm.height (((δ : G1 K (2 + 2)) * x : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)))
        ⟨1, by rintro _ ⟨δ, rfl⟩; exact one_le_height _⟩ ⟨γ, hγ⟩
    have q1 := (qhtBasic K (2 + 2)).1 x
    have w := Real.log_le_log (by linarith) (v.trans u)
    rw [Real.log_mul (by linarith) (by positivity), Real.log_pow, Real.log_exp] at w
    have w' := Real.log_le_sub_one_of_pos (by linarith : 0 < C)
    rw [← hr]
    linarith
  · have := hD (γ * x)
    rw [(qhtBasic K (2 + 2)).2.1 γ hγ x] at this
    linarith [le_abs_self D]

private theorem geo_pk {K : Type} [Field K] [NumberField K] {δ : G1 K (2 + 2)} (h : δ ∈ PK K) : δ ∈ Gam K (2 + 2) := by
  obtain ⟨y, -, rfl⟩ := h
  exact y.2

private theorem geo_cos {K : Type} [Field K] [NumberField K] {q q' : Cos K}
    (h : (q'.out : G1 K (2 + 2)) * (q.out : G1 K (2 + 2))⁻¹ ∈ PK K) : q = q' := by
  obtain ⟨y, hy, e⟩ := h
  have e' : y = q'.out * q.out⁻¹ := Subtype.ext e
  rw [← q.out_eq, ← q'.out_eq]
  exact Quotient.sound (QuotientGroup.rightRel_apply.2 (e' ▸ hy))

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.geo :
    ∀ {K : Type} [Field K] [NumberField K] (ω : Set (AdelicGLn.AdelicGL K (2 + 2))) (t : ℝ), Red ω t → ∃ (ε c Q : ℝ) (M : ℕ), 0 < ε ∧ 0 < c ∧ ∀ (T : ℝ) (x : G1 K (2 + 2)), 0 ≤ T → Q ≤ qht x → ¬ Om T x →
      (∃ (q₀ : Cos K), ∃ δ ∈ PK K, ∃ ρ, Sg ω ρ (δ * qx q₀ x) ∧ Full t ρ ∧ T < HH (qx q₀ x) ∧ qht x ^ c ≤ ρ 1 / ρ 2 ∧ Rat (qht x ^ M) ρ ∧
        ∀ q, q ≠ q₀ → T < HH (qx q x) → Far ω t ε (qx q x)) ∨
      (∃ γ ∈ Gam K (2 + 2), ∃ ρ, ∃ R : ℝ, Sg ω ρ (γ * x) ∧ Full t ρ ∧ 1 ≤ R ∧ Rat R ρ ∧ qht x ^ c ≤ R ∧ (R ^ c ≤ ρ 0 / ρ 1 ∨ R ^ c ≤ ρ 2 / ρ 3) ∧
        ∀ q, T < HH (qx q x) → Far ω t ε (qx q x)) := by
  intro K _ _ ω t hred
  obtain ⟨m, h, E₀, hm, hh, hE₀, hlog⟩ := geo_logs ω hred.bor
  obtain ⟨G, hG⟩ := gain ω t hred.bor hred.pos
  obtain ⟨E, hE⟩ : ∃ E, E = E₀ + |G| + |Real.log t| := ⟨_, rfl⟩
  have hG0 := abs_nonneg G
  have hG1 := le_abs_self G
  have ht0 := abs_nonneg (Real.log t)
  have hEt : |Real.log t| ≤ E := by linarith
  have hE0 : 0 ≤ E := by linarith
  have hEE : E₀ ≤ E := by linarith
  have hGE : G ≤ E := by linarith
  have hm0 : 0 < m := by linarith
  have hd : (1 : ℝ) ≤ (Module.finrank ℚ K : ℝ) := Nat.one_le_cast.2 Module.finrank_pos
  have hε : 6 * m * (1 / (6 * m)) = 1 := by field_simp
  have hc : 2 * (1 / (12 * m * (4 * h + 1))) * (4 * h + 1) = 1 / (6 * m) := by field_simp; norm_num
  have hcm : 12 * (m * (1 / (12 * m * (4 * h + 1)))) ≤ 1 := by
    have : 12 * (m * (1 / (12 * m * (4 * h + 1)))) = 1 / (4 * h + 1) := by field_simp
    rw [this, div_le_one (by linarith)]
    linarith
  have hε0 : 0 < 1 / (6 * m) := by positivity
  have hc0 : 0 < 1 / (12 * m * (4 * h + 1)) := by positivity
  generalize 1 / (6 * m) = ε at hε hc hε0
  generalize 1 / (12 * m * (4 * h + 1)) = c at hc hcm hc0
  refine ⟨ε, c, Real.exp (100 * (m * E) + 1), ⌈h + 2⌉₊, hε0, hc0, fun T x hT hQ hOm => ?_⟩
  have hq0 : 0 < qht x := (Real.exp_pos _).trans_le hQ
  have hl : 100 * (m * E) + 1 ≤ Real.log (qht x) := (Real.le_log_iff_exp_le hq0).2 hQ
  have hl0 : 0 ≤ Real.log (qht x) := Real.log_nonneg ((qhtBasic K (2 + 2)).1 x)
  have hPK := (hpSpec (K := K)).2.2.1
  have hin : ∀ ρ : Fin (2 + 2) → ℝ, (∀ i, 0 < ρ i) → (qht x ^ ε ≤ inR ρ ↔
      ε * Real.log (qht x) ≤ Real.log (ρ 0 / ρ 1) + Real.log (ρ 2 / ρ 3)) := fun ρ hρ => by
    have p1 := div_pos (hρ 0) (hρ 1)
    have p2 := div_pos (hρ 2) (hρ 3)
    rw [inR, ← Real.log_le_log_iff (Real.rpow_pos_of_pos hq0 _) (mul_pos p1 p2), Real.log_rpow hq0,
      Real.log_mul p1.ne' p2.ne']
  let Good : Cos K → Prop := fun q => T < HH (qx q x) ∧ ∃ δ ∈ PK K, ∃ ρ, Sg ω ρ (δ * qx q x) ∧ Rel t ρ ∧
    Real.log (ρ 0 / ρ 1) + Real.log (ρ 2 / ρ 3) < ε * Real.log (qht x)
  have hfar : ∀ q, ¬ Good q → T < HH (qx q x) → Far ω t ε (qx q x) := fun q hq hT' => by
    obtain ⟨δ, hδ, ρ, hS, hR⟩ := hred.rel (qx q x)
    refine ⟨δ, hδ, ρ, hS, hR, ?_⟩
    rw [(qhtBasic K (2 + 2)).2.1 _ q.out.2 x, hin ρ hS.1]
    by_contra hn
    exact hq ⟨hT', δ, hδ, ρ, hS, hR, not_le.1 hn⟩
  have hgood : ∀ (q : Cos K), ∀ δ ∈ PK K, ∀ ρ, T < HH (qx q x) → Sg ω ρ (δ * qx q x) → Rel t ρ →
      Real.log (ρ 0 / ρ 1) + Real.log (ρ 2 / ρ 3) < ε * Real.log (qht x) →
      c * Real.log (qht x) ≤ Real.log (ρ 1 / ρ 2) ∧ E < Real.log (ρ 1 / ρ 2) ∧
        |Real.log (ρ 0 / ρ 1)| + |Real.log (ρ 1 / ρ 2)| + |Real.log (ρ 2 / ρ 3)| ≤ (h + 2) * Real.log (qht x) ∧ Full t ρ := by
    intro q δ hδ ρ hT' hS hR hlt
    have hρ : ∀ i, 0 < ρ i := hS.1
    have hH : 0 < HH (δ * (q.out : G1 K (2 + 2)) * x) := by
      rw [mul_assoc, hPK δ hδ]
      exact hT.trans_lt hT'
    rw [qx, ← mul_assoc] at hS
    obtain ⟨u1, u2, u3⟩ := hlog ρ x _ (mul_mem (geo_pk hδ) q.out.2) hS
    obtain ⟨v1, v2, v3⟩ := geo_good hm hh hE0 hε hcm hd hl (u1.trans hEE) (by linarith) (by linarith)
      ((geo_step hred.pos (hρ 0) (hρ 1) hEt).1 hR.1) ((geo_step hred.pos (hρ 2) (hρ 3) hEt).1 hR.2) hH hlt
    exact ⟨v1, v2, v3, geo_full.2 ⟨hR, (geo_step hred.pos (hρ 1) (hρ 2) hEt).2 v2⟩⟩
  have hgain : ∀ ρ z γ, Sg ω ρ z → Full t ρ → γ ∈ Gam K (2 + 2) → γ ∉ PK K → E < Real.log (ρ 1 / ρ 2) →
      HH (γ * z) < HH z := fun ρ z γ hS hF hγ hn hlt => by
    have := hG ρ z γ hS hF hγ hn
    nlinarith
  by_cases hex : ∃ q, Good q
  · obtain ⟨q₀, hT₀, δ, hδ, ρ, hS, hR, hlt⟩ := hex
    have hρ : ∀ i, 0 < ρ i := hS.1
    obtain ⟨v1, v2, v3, hF⟩ := hgood q₀ δ hδ ρ hT₀ hS hR hlt
    refine Or.inl ⟨q₀, δ, hδ, ρ, hS, hF, hT₀, ?_, fun i j _ => ?_, fun q hq hT' => hfar q ?_ hT'⟩
    · rw [← Real.log_le_log_iff (Real.rpow_pos_of_pos hq0 _) (div_pos (hρ 1) (hρ 2)), Real.log_rpow hq0]
      exact v1
    · refine (geo_ratio hρ i j).trans ?_
      rw [← Real.le_log_iff_exp_le (pow_pos hq0 _), Real.log_pow]
      exact v3.trans (mul_le_mul_of_nonneg_right (Nat.le_ceil _) hl0)
    · rintro ⟨-, δ', hδ', ρ', hS', hR', hlt'⟩
      obtain ⟨-, w2, -, hF'⟩ := hgood q δ' hδ' ρ' hT' hS' hR' hlt'
      have hγ : δ' * (q.out : G1 K (2 + 2)) * (δ * (q₀.out : G1 K (2 + 2)))⁻¹ ∈ Gam K (2 + 2) :=
        mul_mem (mul_mem (geo_pk hδ') q.out.2) (inv_mem (mul_mem (geo_pk hδ) q₀.out.2))
      have hn : δ' * (q.out : G1 K (2 + 2)) * (δ * (q₀.out : G1 K (2 + 2)))⁻¹ ∉ PK K := fun hk => by
        have := mul_mem (mul_mem (inv_mem hδ') hk) hδ
        refine hq (geo_cos (q := q₀) (q' := q) ?_).symm
        convert this using 1
        group
      have k1 := hgain ρ _ _ hS hF hγ hn v2
      have k2 := hgain ρ' _ _ hS' hF' (inv_mem hγ) (fun hk => hn (inv_mem_iff.1 hk)) w2
      have e1 : δ' * (q.out : G1 K (2 + 2)) * (δ * (q₀.out : G1 K (2 + 2)))⁻¹ * (δ * qx q₀ x) = δ' * qx q x := by
        simp only [qx]
        group
      have e2 : (δ' * (q.out : G1 K (2 + 2)) * (δ * (q₀.out : G1 K (2 + 2)))⁻¹)⁻¹ * (δ' * qx q x) = δ * qx q₀ x := by
        simp only [qx]
        group
      rw [e1] at k1
      rw [e2] at k2
      exact lt_asymm k1 k2
  · obtain ⟨γ, hγ, ρ, hS, hF⟩ := hred.full x
    have hρ : ∀ i, 0 < ρ i := hS.1
    obtain ⟨hR, hmid⟩ := geo_full.1 hF
    obtain ⟨u1, u2, u3⟩ := hlog ρ x γ hγ hS
    obtain ⟨v1, v2⟩ := geo_bad hm hh hE0 hc0 hc hcm hd hl (u1.trans hEE) (by linarith) (by linarith)
      ((geo_step hred.pos (hρ 0) (hρ 1) hEt).1 hR.1) ((geo_step hred.pos (hρ 2) (hρ 3) hEt).1 hR.2)
      ((geo_step hred.pos (hρ 1) (hρ 2) hEt).1 hmid)
    refine Or.inr ⟨γ, hγ, ρ, _, hS, hF, Real.one_le_exp (by positivity), fun i j _ => geo_ratio hρ i j, ?_, ?_,
      fun q => hfar q fun hq => hex ⟨q, hq⟩⟩
    · rw [← Real.log_le_iff_le_exp (Real.rpow_pos_of_pos hq0 _), Real.log_rpow hq0]
      exact v1
    · rw [← Real.exp_mul, ← Real.le_log_iff_exp_le (div_pos (hρ 0) (hρ 1)), ← Real.le_log_iff_exp_le (div_pos (hρ 2) (hρ 3)),
        mul_comm _ c]
      by_contra hn
      push Not at hn
      obtain ⟨w1, w2⟩ := v2 hn.1 hn.2
      obtain ⟨q, hq⟩ := not_forall.1 hOm
      have hT' : T < HH (γ * x) := by
        have e : qx q x = (q.out : G1 K (2 + 2)) * γ⁻¹ * (γ * x) := by
          simp only [qx]
          group
        rw [not_le, e] at hq
        by_cases hk : (q.out : G1 K (2 + 2)) * γ⁻¹ ∈ PK K
        · rwa [hPK _ hk] at hq
        · exact hq.trans (hgain ρ _ _ hS hF (mul_mem q.out.2 (inv_mem hγ)) hk w1)
      obtain ⟨δ, hδ, e⟩ := (pkLaws (K := K)).2.2.2 ⟨γ, hγ⟩
      refine hex ⟨Quotient.mk _ ⟨γ, hγ⟩, ?_, δ⁻¹, inv_mem hδ, ρ, ?_, hR, w2⟩
      · rw [qx, e, mul_assoc, hPK δ hδ]
        exact hT'
      · rw [qx, e, mul_assoc, inv_mul_cancel_left]
        exact hS
