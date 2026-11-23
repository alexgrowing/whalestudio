import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsNormalFormStabilizerMeasure
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp

theorem dyad_cauchySchwarz {X : Type} [MeasurableSpace X] (μ : Measure X) (A B : X → ℝ)
    (hA : Measurable A) (hB : Measurable B) (P Q : ℝ) (hP : 0 < P) (hQ : 0 < Q)
    (h1 : ∫⁻ x, ENNReal.ofReal (A x ^ 2) ∂μ ≤ ENNReal.ofReal (P ^ 2))
    (h2 : ∫⁻ x, ENNReal.ofReal (B x ^ 2) ∂μ ≤ ENNReal.ofReal (Q ^ 2)) :
    ∫⁻ x, ENNReal.ofReal (A x * B x) ∂μ ≤ ENNReal.ofReal (P * Q) := by
  have hc : 0 < Q / (2 * P) := by positivity
  have hd : 0 < P / (2 * Q) := by positivity
  have hpt : ∀ x, ENNReal.ofReal (A x * B x) ≤
      ENNReal.ofReal (Q / (2 * P)) * ENNReal.ofReal (A x ^ 2)
        + ENNReal.ofReal (P / (2 * Q)) * ENNReal.ofReal (B x ^ 2) := by
    intro x
    rw [← ENNReal.ofReal_mul hc.le, ← ENNReal.ofReal_mul hd.le,
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have : Q / (2 * P) * A x ^ 2 + P / (2 * Q) * B x ^ 2 - A x * B x
        = (Q * A x - P * B x) ^ 2 / (2 * P * Q) := by
      field_simp; ring
    have h0 : 0 ≤ (Q * A x - P * B x) ^ 2 / (2 * P * Q) := by positivity
    linarith
  have mA : Measurable fun x => ENNReal.ofReal (A x ^ 2) := by fun_prop
  have mB : Measurable fun x => ENNReal.ofReal (B x ^ 2) := by fun_prop
  calc _ ≤ _ := lintegral_mono hpt
    _ = ENNReal.ofReal (Q / (2 * P)) * ∫⁻ x, ENNReal.ofReal (A x ^ 2) ∂μ
        + ENNReal.ofReal (P / (2 * Q)) * ∫⁻ x, ENNReal.ofReal (B x ^ 2) ∂μ := by
      rw [lintegral_add_left (mA.const_mul _), lintegral_const_mul _ mA, lintegral_const_mul _ mB]
    _ ≤ ENNReal.ofReal (Q / (2 * P)) * ENNReal.ofReal (P ^ 2)
        + ENNReal.ofReal (P / (2 * Q)) * ENNReal.ofReal (Q ^ 2) := by gcongr
    _ = _ := by
      rw [← ENNReal.ofReal_mul hc.le, ← ENNReal.ofReal_mul hd.le,
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      field_simp; ring

theorem dyad_exists_shell (H s : ℝ) (hH : 0 < H) :
    ∃ i : ℕ, s ≤ 2 ^ (i + 1) * H ∧ (i = 0 ∨ 2 ^ i * H < s) := by
  have hex : ∃ i : ℕ, s ≤ 2 ^ (i + 1) * H := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (s / H) (one_lt_two (α := ℝ))
    refine ⟨n, ?_⟩
    rw [div_lt_iff₀ hH] at hn
    have : (0:ℝ) < 2 ^ n * H := by positivity
    rw [pow_succ]; linarith
  classical
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  rcases h : Nat.find hex with _ | k
  · exact Or.inl rfl
  · right
    have := Nat.find_min hex (m := k) (by omega)
    exact not_le.mp this

theorem dyad_exists_down (M y : ℝ) (hy : 0 < y) (hM : y ≤ M) :
    ∃ a : ℕ, M / 2 ^ (a + 1) < y ∧ y ≤ 2 * (M / 2 ^ (a + 1)) := by
  obtain ⟨n, h1, h2⟩ := exists_nat_pow_near (x := M / y) (y := 2)
    (by rw [le_div_iff₀ hy]; linarith) one_lt_two
  refine ⟨n, ?_, ?_⟩
  · rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hy] at h2; linarith
  · rw [le_div_iff₀ hy] at h1
    have : 2 * (M / 2 ^ (n + 1)) = M / 2 ^ n := by field_simp; ring
    rw [this, le_div_iff₀ (by positivity)]; linarith

theorem dyad_piece_real (r k e n : ℕ) (H De N sg u v w : ℝ) (hr : 1 ≤ r) (hH : 0 < H)
    (hDe : 0 < De) (hN : 0 < N) (hsg : 1 ≤ sg) (hu : 0 < u) (hv : 0 < v) (hw : 0 < w)
    (hwN : w ≤ N) (hwM : w ≤ ((u * (2 * H)) ^ r * De) ^ 2 * v)
    (hNR : 1 ≤ N * (u * (2 * H)) ^ (2 * r)) (hsu : sg ≤ u ^ r) :
    (u * (2 * H)) ^ e * w ^ (k + 1) * (u ^ (e + 4 * r + 1 + n))⁻¹ ≤
      (2 * H) ^ (e + 4 * r) * De ^ 2 * N ^ (k + 1) * sg ^ (-((n : ℝ) / r)) * (u⁻¹ * v) := by
  have hr' : (0:ℝ) < r := by exact_mod_cast hr
  have h1 : (u ^ n)⁻¹ ≤ sg ^ (-((n : ℝ) / r)) := by
    rw [Real.rpow_neg (by linarith)]
    apply inv_anti₀ (by positivity)
    calc sg ^ ((n : ℝ) / r) ≤ (u ^ r) ^ ((n : ℝ) / r) := by gcongr
      _ = u ^ n := by
        rw [← Real.rpow_natCast u r, ← Real.rpow_mul hu.le, ← Real.rpow_natCast u n]
        congr 1; field_simp
  have h2 : w ^ (k + 1) ≤ N ^ (k + 1) * (u * (2 * H)) ^ (4 * r) * De ^ 2 * v := by
    calc w ^ (k + 1) = w ^ k * w * 1 := by ring
      _ ≤ N ^ k * (((u * (2 * H)) ^ r * De) ^ 2 * v) * (N * (u * (2 * H)) ^ (2 * r)) := by
        gcongr
      _ = _ := by ring
  calc _ ≤ (u * (2 * H)) ^ e * (N ^ (k + 1) * (u * (2 * H)) ^ (4 * r) * De ^ 2 * v)
        * (u ^ (e + 4 * r + 1 + n))⁻¹ := by gcongr
    _ = (2 * H) ^ (e + 4 * r) * De ^ 2 * N ^ (k + 1) * (u ^ n)⁻¹ * (u⁻¹ * v) := by
      rw [mul_pow u, mul_pow u]
      field_simp
      ring
    _ ≤ _ := by gcongr

theorem dyad_tsum_four (c : ℝ≥0∞) :
    ∑' p : ℕ × ℕ × ℕ × ℕ, c * (2⁻¹ ^ p.1 * (2⁻¹ ^ p.2.1 * (2⁻¹ ^ p.2.2.1 * 2⁻¹ ^ p.2.2.2)))
      = 16 * c := by
  have g : ∑' n : ℕ, (2⁻¹ : ℝ≥0∞) ^ n = 2 := by
    rw [ENNReal.tsum_geometric]; simp
  rw [ENNReal.tsum_mul_left]
  simp only [ENNReal.tsum_prod', ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, g]
  ring

theorem dyadic_summation : ∀ (X : Type) [MeasurableSpace X] (ν : Measure X) (A B S S' Y Y' : X → ℝ) (r j kk e q : ℕ) (H₁ De D K K' sg : ℝ), Measurable A → Measurable B → Measurable S → Measurable S' → Measurable Y → Measurable Y' → 1 ≤ r → 1 ≤ kk → e + 4 * r + 2 ≤ q → 1 ≤ H₁ → 1 ≤ De → 0 < D → 0 < K → 0 < K' → 1 ≤ sg → (∀ᵐ x ∂ν, 0 ≤ A x ∧ 0 ≤ B x ∧ 1 ≤ S x ∧ 1 ≤ S' x ∧ 0 < Y x ∧ 0 < Y' x ∧ Y x * Y' x * D ≤ 2 ^ j ∧ D ≤ (S x * S' x) ^ r ∧ Y x ≤ max (S x) (S' x) ^ r * De ∧ Y' x ≤ max (S x) (S' x) ^ r * De ∧ sg ≤ max 1 ((S x * S' x) ^ r / (2 * H₁) ^ (2 * r))) → (∀ (i i' : ℕ) (y : ℝ), 0 < y → ∫⁻ x in {x | S x ≤ 2 ^ (i + 1) * H₁ ∧ (i = 0 ∨ 2 ^ i * H₁ < S x) ∧ S' x ≤ 2 ^ (i' + 1) * H₁ ∧ y < Y x ∧ Y x ≤ 2 * y}, ENNReal.ofReal (A x ^ 2) ∂ν ≤ ENNReal.ofReal (K * (2 ^ (i + i' + 1) * H₁) ^ e * y ^ (2 * kk) * (((2 : ℝ) ^ i) ^ (2 * q))⁻¹)) → (∀ (i i' : ℕ) (y : ℝ), 0 < y → ∫⁻ x in {x | S' x ≤ 2 ^ (i' + 1) * H₁ ∧ (i' = 0 ∨ 2 ^ i' * H₁ < S' x) ∧ S x ≤ 2 ^ (i + 1) * H₁ ∧ y < Y' x ∧ Y' x ≤ 2 * y}, ENNReal.ofReal (B x ^ 2) ∂ν ≤ ENNReal.ofReal (K' * (2 ^ (i + i' + 1) * H₁) ^ e * y ^ (2 * kk) * (((2 : ℝ) ^ i') ^ (2 * q))⁻¹)) → ∫⁻ x, ENNReal.ofReal (A x * B x) ∂ν ≤ ENNReal.ofReal (16 * Real.sqrt (K * K') * (2 * H₁) ^ (e + 4 * r) * De ^ 2 * (2 ^ j / D) ^ kk * sg ^ (-(((q : ℝ) - e - 4 * r - 1) / r))) := by
  intro X _ ν A B S S' Y Y' r j kk e q H₁ De D K K' sg hA hB _ _ _ _ hr hkk hq hH hDe hD hK hK'
    hsg hae h1 h2
  obtain ⟨k, rfl⟩ : ∃ k, kk = k + 1 := ⟨kk - 1, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n, q = e + 4 * r + 1 + n := ⟨q - (e + 4 * r + 1), by omega⟩
  have hexp : ((e + 4 * r + 1 + n : ℕ) : ℝ) - e - 4 * r - 1 = n := by push_cast; ring
  rw [hexp]
  have hH0 : 0 < H₁ := by linarith
  have hDe0 : 0 < De := by linarith
  set C : ℝ := Real.sqrt (K * K') * ((2 * H₁) ^ (e + 4 * r) * De ^ 2 * (2 ^ j / D) ^ (k + 1)
    * sg ^ (-((n : ℝ) / r))) with hC
  have hC0 : 0 ≤ C := by positivity
  let M : ℕ → ℕ → ℝ := fun i i' => (2 ^ (i + i' + 1) * H₁) ^ r * De
  have hM0 : ∀ i i', 0 < M i i' := fun i i' => by positivity
  let P : ℕ × ℕ × ℕ × ℕ → Set X := fun p => {x |
    (0 ≤ A x ∧ 0 ≤ B x ∧ 1 ≤ S x ∧ 1 ≤ S' x ∧ 0 < Y x ∧ 0 < Y' x ∧ Y x * Y' x * D ≤ 2 ^ j ∧ D ≤ (S x * S' x) ^ r ∧ Y x ≤ max (S x) (S' x) ^ r * De ∧ Y' x ≤ max (S x) (S' x) ^ r * De ∧ sg ≤ max 1 ((S x * S' x) ^ r / (2 * H₁) ^ (2 * r))) ∧
    (S x ≤ 2 ^ (p.1 + 1) * H₁ ∧ (p.1 = 0 ∨ 2 ^ p.1 * H₁ < S x)) ∧
    (S' x ≤ 2 ^ (p.2.1 + 1) * H₁ ∧ (p.2.1 = 0 ∨ 2 ^ p.2.1 * H₁ < S' x)) ∧
    (M p.1 p.2.1 / 2 ^ (p.2.2.1 + 1) < Y x ∧ Y x ≤ 2 * (M p.1 p.2.1 / 2 ^ (p.2.2.1 + 1))) ∧
    (M p.1 p.2.1 / 2 ^ (p.2.2.2 + 1) < Y' x ∧ Y' x ≤ 2 * (M p.1 p.2.1 / 2 ^ (p.2.2.2 + 1)))}
  have hcov : ∀ᵐ x ∂ν, x ∈ ⋃ p, P p := by
    filter_upwards [hae] with x hx
    obtain ⟨i, hi⟩ := dyad_exists_shell H₁ (S x) hH0
    obtain ⟨i', hi'⟩ := dyad_exists_shell H₁ (S' x) hH0
    have hmax : max (S x) (S' x) ^ r * De ≤ M i i' := by
      have a1 : (2:ℝ) ^ (i + 1) ≤ 2 ^ (i + i' + 1) := pow_le_pow_right₀ one_le_two (by omega)
      have a2 : (2:ℝ) ^ (i' + 1) ≤ 2 ^ (i + i' + 1) := pow_le_pow_right₀ one_le_two (by omega)
      have a3 : max (S x) (S' x) ≤ 2 ^ (i + i' + 1) * H₁ :=
        max_le (hi.1.trans (by gcongr)) (hi'.1.trans (by gcongr))
      have a4 : 0 ≤ max (S x) (S' x) := le_max_of_le_left (by linarith [hx.2.2.1])
      show _ ≤ (2 ^ (i + i' + 1) * H₁) ^ r * De
      gcongr
    obtain ⟨a, ha⟩ := dyad_exists_down (M i i') (Y x) hx.2.2.2.2.1
      (hx.2.2.2.2.2.2.2.2.1.trans hmax)
    obtain ⟨b, hb⟩ := dyad_exists_down (M i i') (Y' x) hx.2.2.2.2.2.1
      (hx.2.2.2.2.2.2.2.2.2.1.trans hmax)
    exact Set.mem_iUnion.2 ⟨(i, i', a, b), hx, hi, hi', ha, hb⟩
  have hpiece : ∀ p : ℕ × ℕ × ℕ × ℕ, ∫⁻ x in P p, ENNReal.ofReal (A x * B x) ∂ν ≤
      ENNReal.ofReal C * (2⁻¹ ^ p.1 * (2⁻¹ ^ p.2.1 * (2⁻¹ ^ p.2.2.1 * 2⁻¹ ^ p.2.2.2))) := by
    rintro ⟨i, i', a, b⟩
    rcases (P (i, i', a, b)).eq_empty_or_nonempty with he | ⟨x, hx⟩
    · rw [he]; simp
    obtain ⟨⟨-, -, s1, s2, y1, y2, g1, g2, -, -, g3⟩, ⟨b1, -⟩, ⟨b2, -⟩, ⟨c1, -⟩, ⟨c2, -⟩⟩ := hx
    simp only at b1 b2 c1 c2 ⊢
    have hm := hM0 i i'
    set y : ℝ := M i i' / 2 ^ (a + 1) with hy
    set y' : ℝ := M i i' / 2 ^ (b + 1) with hy'
    have hy0 : 0 < y := by positivity
    have hy0' : 0 < y' := by positivity
    set R : ℝ := 2 ^ (i + i' + 1) * H₁ with hR
    have hR0 : 0 < R := by positivity
    set q := e + 4 * r + 1 + n with hqdef
    have i1 : ∫⁻ x in P (i, i', a, b), ENNReal.ofReal (A x ^ 2) ∂ν ≤
        ENNReal.ofReal ((Real.sqrt K * Real.sqrt (R ^ e) * y ^ (k + 1) * (((2:ℝ) ^ i) ^ q)⁻¹) ^ 2) := by
      refine le_trans (lintegral_mono_set ?_) ((h1 i i' y hy0).trans (le_of_eq ?_))
      · intro z hz
        exact ⟨hz.2.1.1, hz.2.1.2, hz.2.2.1.1, hz.2.2.2.1.1, hz.2.2.2.1.2⟩
      · congr 1
        rw [← hR, mul_pow _ _ 2, mul_pow _ _ 2, mul_pow _ _ 2, Real.sq_sqrt hK.le, Real.sq_sqrt (by positivity), inv_pow,
          ← pow_mul y, ← pow_mul _ q, mul_comm q 2, mul_comm (k + 1) 2]
    have i2 : ∫⁻ x in P (i, i', a, b), ENNReal.ofReal (B x ^ 2) ∂ν ≤
        ENNReal.ofReal ((Real.sqrt K' * Real.sqrt (R ^ e) * y' ^ (k + 1) * (((2:ℝ) ^ i') ^ q)⁻¹) ^ 2) := by
      refine le_trans (lintegral_mono_set ?_) ((h2 i i' y' hy0').trans (le_of_eq ?_))
      · intro z hz
        exact ⟨hz.2.2.1.1, hz.2.2.1.2, hz.2.1.1, hz.2.2.2.2.1, hz.2.2.2.2.2⟩
      · congr 1
        rw [← hR, mul_pow _ _ 2, mul_pow _ _ 2, mul_pow _ _ 2, Real.sq_sqrt hK'.le, Real.sq_sqrt (by positivity), inv_pow,
          ← pow_mul y', ← pow_mul _ q, mul_comm q 2, mul_comm (k + 1) 2]
    refine (dyad_cauchySchwarz _ A B hA hB _ _ (by positivity) (by positivity) i1 i2).trans ?_
    have hrhs : ENNReal.ofReal C * (2⁻¹ ^ i * (2⁻¹ ^ i' * (2⁻¹ ^ a * 2⁻¹ ^ b))) =
        ENNReal.ofReal (C * (((2:ℝ) ^ (i + i'))⁻¹ * ((2:ℝ) ^ (a + b))⁻¹)) := by
      have e2 : (2⁻¹ : ℝ≥0∞) = ENNReal.ofReal (2⁻¹ : ℝ) := by
        rw [ENNReal.ofReal_inv_of_pos two_pos]; simp
      rw [ENNReal.ofReal_mul hC0, e2]
      congr 1
      simp only [← ENNReal.ofReal_pow (show (0:ℝ) ≤ 2⁻¹ by norm_num)]
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [pow_add, pow_add]; simp only [inv_pow]; field_simp
    rw [hrhs]
    apply ENNReal.ofReal_le_ofReal
    have hRu : R = 2 ^ (i + i') * (2 * H₁) := by rw [hR]; ring
    have hu1 : (1:ℝ) ≤ 2 ^ (i + i') := one_le_pow₀ one_le_two
    have hSS : S x * S' x ≤ 2 ^ (i + i') * (2 * H₁) ^ 2 := by
      calc S x * S' x ≤ (2 ^ (i + 1) * H₁) * (2 ^ (i' + 1) * H₁) := by
            apply mul_le_mul b1 b2 (by linarith) (by positivity)
        _ = _ := by ring
    have hSS0 : 0 ≤ S x * S' x := mul_nonneg (by linarith) (by linarith)
    have hSSr : (S x * S' x) ^ r ≤ (2 ^ (i + i')) ^ r * (2 * H₁) ^ (2 * r) := by
      rw [pow_mul, ← mul_pow]; gcongr
    have key := dyad_piece_real r k e n H₁ De (2 ^ j / D) sg (2 ^ (i + i')) ((2 ^ (a + b))⁻¹)
      (y * y') hr hH0 hDe0 (by positivity) hsg (by positivity) (by positivity) (by positivity)
      (by
        rw [le_div_iff₀ hD]
        refine le_trans ?_ g1
        gcongr)
      (by
        rw [← hRu]
        have : y * y' = (R ^ r * De) ^ 2 * (2 ^ (a + b))⁻¹ / 4 := by
          rw [hy, hy']
          show (R ^ r * De) / _ * ((R ^ r * De) / _) = _
          field_simp; ring
        rw [this]
        have : 0 ≤ (R ^ r * De) ^ 2 * ((2:ℝ) ^ (a + b))⁻¹ := by positivity
        linarith)
      (by
        rw [div_mul_eq_mul_div, le_div_iff₀ hD, one_mul]
        have j1 : (1:ℝ) ≤ 2 ^ j := one_le_pow₀ one_le_two
        have : ((2:ℝ) ^ (i + i')) ^ r ≤ (2 ^ (i + i')) ^ (2 * r) :=
          pow_le_pow_right₀ hu1 (by omega)
        calc D ≤ (2 ^ (i + i')) ^ r * (2 * H₁) ^ (2 * r) := g2.trans hSSr
          _ ≤ (2 ^ (i + i')) ^ (2 * r) * (2 * H₁) ^ (2 * r) := by gcongr
          _ = 1 * (2 ^ (i + i') * (2 * H₁)) ^ (2 * r) := by rw [mul_pow _ (2 * H₁), one_mul]
          _ ≤ _ := by gcongr)
      (by
        refine g3.trans (max_le (one_le_pow₀ hu1) ?_)
        rw [div_le_iff₀ (by positivity)]
        exact hSSr)
    rw [← hRu, ← hqdef] at key
    have hsq : Real.sqrt (R ^ e) * Real.sqrt (R ^ e) = R ^ e := Real.mul_self_sqrt (by positivity)
    calc _ = Real.sqrt (K * K') * ((Real.sqrt (R ^ e) * Real.sqrt (R ^ e)) * (y * y') ^ (k + 1)
            * (((2:ℝ) ^ (i + i')) ^ q)⁻¹) := by
          rw [Real.sqrt_mul hK.le, mul_pow y, pow_add 2 i i', mul_pow _ _ q, mul_inv]; ring
      _ ≤ Real.sqrt (K * K') * ((2 * H₁) ^ (e + 4 * r) * De ^ 2 * (2 ^ j / D) ^ (k + 1)
            * sg ^ (-((n : ℝ) / r)) * (((2:ℝ) ^ (i + i'))⁻¹ * ((2:ℝ) ^ (a + b))⁻¹)) := by
          rw [hsq]; gcongr
      _ = _ := by rw [hC]; ring
  calc _ = ∫⁻ x in ⋃ p, P p, ENNReal.ofReal (A x * B x) ∂ν := by
        rw [Measure.restrict_eq_self_of_ae_mem hcov]
    _ ≤ _ := lintegral_iUnion_le _ _
    _ ≤ _ := ENNReal.tsum_le_tsum hpiece
    _ = 16 * ENNReal.ofReal C := dyad_tsum_four _
    _ = ENNReal.ofReal (16 * C) := by
        rw [ENNReal.ofReal_mul (show (0:ℝ) ≤ 16 by norm_num), ENNReal.ofReal_ofNat]
    _ = _ := by rw [hC]; congr 1; ring

end GlobalTheory.Amp
