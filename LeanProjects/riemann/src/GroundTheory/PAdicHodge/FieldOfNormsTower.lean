import Mathlib
import GroundTheory.LocalFields.SeparableClosure
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace GroundTheory.PAdicHodge

open GroundTheory.LocalField ValuativeRel Filter Topology

section Nrm

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]

def nrm (x : Ω) : ℝ :=
  letI := normedField K
  spectralNorm K Ω x

variable {K}

theorem nrm_def (x : Ω) : nrm K x = (letI := algebraicNormedField K Ω; ‖x‖) :=
  rfl

theorem nrm_nonneg (x : Ω) : 0 ≤ nrm K x := by
  letI := algebraicNormedField K Ω
  change 0 ≤ ‖x‖
  exact norm_nonneg x

@[simp]
theorem nrm_zero : nrm K (0 : Ω) = 0 := by
  letI := algebraicNormedField K Ω
  change ‖(0 : Ω)‖ = 0
  exact norm_zero

@[simp]
theorem nrm_one : nrm K (1 : Ω) = 1 := by
  letI := algebraicNormedField K Ω
  change ‖(1 : Ω)‖ = 1
  exact norm_one

theorem nrm_mul (x y : Ω) : nrm K (x * y) = nrm K x * nrm K y := by
  letI := algebraicNormedField K Ω
  change ‖x * y‖ = ‖x‖ * ‖y‖
  exact norm_mul x y

theorem nrm_pow (x : Ω) (n : ℕ) : nrm K (x ^ n) = nrm K x ^ n := by
  letI := algebraicNormedField K Ω
  change ‖x ^ n‖ = ‖x‖ ^ n
  exact norm_pow x n

@[simp]
theorem nrm_neg (x : Ω) : nrm K (-x) = nrm K x := by
  letI := algebraicNormedField K Ω
  change ‖-x‖ = ‖x‖
  exact norm_neg x

theorem nrm_sub_comm (x y : Ω) : nrm K (x - y) = nrm K (y - x) := by
  rw [← neg_sub, nrm_neg]

@[simp]
theorem nrm_eq_zero {x : Ω} : nrm K x = 0 ↔ x = 0 := by
  letI := algebraicNormedField K Ω
  change ‖x‖ = 0 ↔ x = 0
  exact norm_eq_zero

theorem nrm_pos {x : Ω} : 0 < nrm K x ↔ x ≠ 0 := by
  letI := algebraicNormedField K Ω
  change 0 < ‖x‖ ↔ x ≠ 0
  exact norm_pos_iff

theorem nrm_inv (x : Ω) : nrm K x⁻¹ = (nrm K x)⁻¹ := by
  letI := algebraicNormedField K Ω
  change ‖x⁻¹‖ = ‖x‖⁻¹
  exact norm_inv x

theorem nrm_div (x y : Ω) : nrm K (x / y) = nrm K x / nrm K y := by
  letI := algebraicNormedField K Ω
  change ‖x / y‖ = ‖x‖ / ‖y‖
  exact norm_div x y

theorem nrm_add_le_max (x y : Ω) : nrm K (x + y) ≤ max (nrm K x) (nrm K y) := by
  letI := algebraicNormedField K Ω
  haveI := algebraicNormedField_isUltrametricDist K Ω
  change ‖x + y‖ ≤ max ‖x‖ ‖y‖
  exact IsUltrametricDist.norm_add_le_max x y

theorem nrm_sub_le_max (x y : Ω) : nrm K (x - y) ≤ max (nrm K x) (nrm K y) := by
  rw [sub_eq_add_neg, ← nrm_neg y]
  exact nrm_add_le_max x (-y)

theorem nrm_add_le_of_le {x y : Ω} {r : ℝ} (hx : nrm K x ≤ r) (hy : nrm K y ≤ r) :
    nrm K (x + y) ≤ r :=
  (nrm_add_le_max x y).trans (max_le hx hy)

theorem nrm_sub_le_of_le {x y : Ω} {r : ℝ} (hx : nrm K x ≤ r) (hy : nrm K y ≤ r) :
    nrm K (x - y) ≤ r :=
  (nrm_sub_le_max x y).trans (max_le hx hy)

theorem nrm_sub_le_of_le' {x y z : Ω} {r : ℝ} (h₁ : nrm K (x - y) ≤ r) (h₂ : nrm K (y - z) ≤ r) :
    nrm K (x - z) ≤ r := by
  have : x - z = (x - y) + (y - z) := by ring
  rw [this]
  exact nrm_add_le_of_le h₁ h₂

theorem abs_nrm_sub_nrm_le (x y : Ω) : |nrm K x - nrm K y| ≤ nrm K (x - y) := by
  letI := algebraicNormedField K Ω
  change |‖x‖ - ‖y‖| ≤ ‖x - y‖
  exact abs_norm_sub_norm_le x y

theorem nrm_add_eq_left {x y : Ω} (h : nrm K y < nrm K x) : nrm K (x + y) = nrm K x := by
  letI := algebraicNormedField K Ω
  haveI := algebraicNormedField_isUltrametricDist K Ω
  change ‖y‖ < ‖x‖ at h
  change ‖x + y‖ = ‖x‖
  exact IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (ne_of_gt h) |>.trans (max_eq_left h.le)

theorem nrm_prod {ι : Type*} (s : Finset ι) (f : ι → Ω) :
    nrm K (∏ i ∈ s, f i) = ∏ i ∈ s, nrm K (f i) := by
  letI := algebraicNormedField K Ω
  change ‖∏ i ∈ s, f i‖ = ∏ i ∈ s, ‖f i‖
  exact norm_prod s f

theorem nrm_sum_le {ι : Type*} {s : Finset ι} {f : ι → Ω} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ i ∈ s, nrm K (f i) ≤ C) : nrm K (∑ i ∈ s, f i) ≤ C := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hC
  | insert j s hj ih =>
    rw [Finset.sum_insert hj]
    exact nrm_add_le_of_le (h j (Finset.mem_insert_self _ _))
      (ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi))

theorem nrm_algebraMap (a : K) : nrm K (algebraMap K Ω a) = (letI := normedField K; ‖a‖) := by
  letI := normedField K
  exact spectralNorm_extends a

theorem nrm_natCast_le_one (n : ℕ) : nrm K (n : Ω) ≤ 1 := by
  letI := algebraicNormedField K Ω
  haveI := algebraicNormedField_isUltrametricDist K Ω
  change ‖(n : Ω)‖ ≤ 1
  exact IsUltrametricDist.norm_natCast_le_one Ω n

theorem nrm_intCast_le_one (n : ℤ) : nrm K (n : Ω) ≤ 1 := by
  letI := algebraicNormedField K Ω
  haveI := algebraicNormedField_isUltrametricDist K Ω
  change ‖(n : Ω)‖ ≤ 1
  exact IsUltrametricDist.norm_intCast_le_one Ω n

theorem nrm_algEquiv (σ : Ω ≃ₐ[K] Ω) (x : Ω) : nrm K (σ x) = nrm K x := by
  letI := normedField K
  exact (spectralNorm_eq_of_equiv σ x).symm

variable (K Ω) in

theorem exists_nrm_algebraMap_lt {ε : ℝ} (hε : 0 < ε) :
    ∃ a : K, a ≠ 0 ∧ nrm K (algebraMap K Ω a) < ε := by
  letI := normedField K
  obtain ⟨a, ha0, ha1⟩ := NormedField.exists_norm_lt_one K
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε ha1
  refine ⟨a ^ n, pow_ne_zero _ (norm_pos_iff.mp ha0), ?_⟩
  rw [nrm_algebraMap, norm_pow]
  exact hn

variable [ValuativeRel Ω] [ValuativeExtension K Ω]

theorem nrm_le_nrm_iff (x y : Ω) : nrm K x ≤ nrm K y ↔ x ≤ᵥ y :=
  (vle_iff_spectralNorm_le (K := K) x y).symm

theorem nrm_le_nrm_iff_valuation (x y : Ω) :
    nrm K x ≤ nrm K y ↔ valuation Ω x ≤ valuation Ω y := by
  rw [nrm_le_nrm_iff, (valuation Ω).vle_iff_le]

theorem nrm_lt_nrm_iff_valuation (x y : Ω) :
    nrm K x < nrm K y ↔ valuation Ω x < valuation Ω y := by
  rw [← not_le, ← not_le, nrm_le_nrm_iff_valuation]

theorem nrm_le_one_iff (x : Ω) : nrm K x ≤ 1 ↔ valuation Ω x ≤ 1 := by
  rw [← nrm_one (K := K) (Ω := Ω), nrm_le_nrm_iff_valuation, map_one]

theorem nrm_lt_one_iff (x : Ω) : nrm K x < 1 ↔ valuation Ω x < 1 := by
  rw [← nrm_one (K := K) (Ω := Ω), nrm_lt_nrm_iff_valuation, map_one]

variable [TopologicalSpace Ω] [IsValuativeTopology Ω]

variable (K Ω) in

theorem continuous_nrm : Continuous (nrm K : Ω → ℝ) := by
  rw [continuous_iff_continuousAt]
  intro x
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨a, ha0, ha⟩ := exists_nrm_algebraMap_lt K Ω hε
  have hv : valuation Ω (algebraMap K Ω a) ≠ 0 := by
    simpa using (FaithfulSMul.algebraMap_injective K Ω).ne ha0
  have hmem := (IsValuativeTopology.hasBasis_nhds x).mem_of_mem (i := Units.mk0 _ hv) trivial
  filter_upwards [hmem] with y hy
  simp only [Units.val_mk0] at hy
  rw [Real.dist_eq]
  refine lt_of_le_of_lt (abs_nrm_sub_nrm_le y x) (lt_of_lt_of_le ?_ ha.le)
  exact (nrm_lt_nrm_iff_valuation _ _).mpr hy

end Nrm

section Estimates

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]

theorem nrm_prod_sub_prod_le {ι : Type*} (s : Finset ι) (a b : ι → Ω) {δ : ℝ} (hδ : 0 ≤ δ)
    (ha : ∀ i ∈ s, nrm K (a i) ≤ 1) (hb : ∀ i ∈ s, nrm K (b i) ≤ 1)
    (h : ∀ i ∈ s, nrm K (a i - b i) ≤ δ) :
    nrm K (∏ i ∈ s, a i - ∏ i ∈ s, b i) ≤ δ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hδ
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj]
    have e : a j * ∏ i ∈ s, a i - b j * ∏ i ∈ s, b i =
        a j * (∏ i ∈ s, a i - ∏ i ∈ s, b i) + (a j - b j) * ∏ i ∈ s, b i := by ring
    rw [e]
    have h1 := ih (fun i hi ↦ ha i (Finset.mem_insert_of_mem hi))
      (fun i hi ↦ hb i (Finset.mem_insert_of_mem hi)) (fun i hi ↦ h i (Finset.mem_insert_of_mem hi))
    have h2 : ∏ i ∈ s, nrm K (b i) ≤ 1 :=
      Finset.prod_le_one (fun i _ ↦ nrm_nonneg _) (fun i hi ↦ hb i (Finset.mem_insert_of_mem hi))
    refine nrm_add_le_of_le ?_ ?_
    · rw [nrm_mul]
      calc nrm K (a j) * nrm K (∏ i ∈ s, a i - ∏ i ∈ s, b i) ≤ 1 * δ :=
            mul_le_mul (ha j (Finset.mem_insert_self _ _)) h1 (nrm_nonneg _) zero_le_one
        _ = δ := one_mul δ
    · rw [nrm_mul, nrm_prod]
      calc nrm K (a j - b j) * ∏ i ∈ s, nrm K (b i) ≤ δ * 1 :=
            mul_le_mul (h j (Finset.mem_insert_self _ _)) h2
              (Finset.prod_nonneg fun i _ ↦ nrm_nonneg _) hδ
        _ = δ := mul_one δ

theorem nrm_pow_sub_pow_le {a b : Ω} (ha : nrm K a ≤ 1) (hb : nrm K b ≤ 1) (n : ℕ) :
    nrm K (a ^ n - b ^ n) ≤ nrm K (a - b) := by
  rw [← geom_sum₂_mul, nrm_mul]
  have : nrm K (∑ i ∈ Finset.range n, a ^ i * b ^ (n - 1 - i)) ≤ 1 := by
    refine nrm_sum_le zero_le_one fun i _ ↦ ?_
    rw [nrm_mul, nrm_pow, nrm_pow]
    exact mul_le_one₀ (pow_le_one₀ (nrm_nonneg _) ha) (pow_nonneg (nrm_nonneg _) _)
      (pow_le_one₀ (nrm_nonneg _) hb)
  calc _ ≤ 1 * nrm K (a - b) := mul_le_mul_of_nonneg_right this (nrm_nonneg _)
    _ = _ := one_mul _

theorem nrm_le_one_of_pow {a : Ω} (ha : nrm K a ≤ 1) (n : ℕ) : nrm K (a ^ n) ≤ 1 := by
  rw [nrm_pow]; exact pow_le_one₀ (nrm_nonneg _) ha

theorem nrm_add_le_one {a b : Ω} (ha : nrm K a ≤ 1) (hb : nrm K b ≤ 1) : nrm K (a + b) ≤ 1 :=
  nrm_add_le_of_le ha hb

theorem nrm_mul_le_one {a b : Ω} (ha : nrm K a ≤ 1) (hb : nrm K b ≤ 1) : nrm K (a * b) ≤ 1 := by
  rw [nrm_mul]; exact mul_le_one₀ ha (nrm_nonneg _) hb

variable {p : ℕ}

theorem nrm_binomialSum_le (x y : Ω) (hx : nrm K x ≤ 1) (hy : nrm K y ≤ 1) :
    nrm K (∑ k ∈ Finset.Ioo 0 p, x ^ (k - 1) * y ^ (p - k - 1) * ((p.choose k / p : ℕ) : Ω)) ≤ 1 := by
  refine nrm_sum_le zero_le_one fun k _ ↦ ?_
  exact nrm_mul_le_one (nrm_mul_le_one (nrm_le_one_of_pow hx _) (nrm_le_one_of_pow hy _))
    (nrm_natCast_le_one _)

theorem nrm_add_pow_prime_sub_le (hp : p.Prime) {a b : Ω} (ha : nrm K a ≤ 1) (hb : nrm K b ≤ 1) :
    nrm K ((a + b) ^ p - a ^ p - b ^ p) ≤ nrm K (p : Ω) := by
  rw [add_pow_prime_eq hp a b]
  have e : a ^ p + b ^ p + (p : Ω) * a * b *
      ∑ k ∈ Finset.Ioo 0 p, a ^ (k - 1) * b ^ (p - k - 1) * ((p.choose k / p : ℕ) : Ω) - a ^ p - b ^ p
      = (p : Ω) * (a * b * ∑ k ∈ Finset.Ioo 0 p, a ^ (k - 1) * b ^ (p - k - 1) *
        ((p.choose k / p : ℕ) : Ω)) := by ring
  rw [e, nrm_mul]
  have := nrm_mul_le_one (nrm_mul_le_one ha hb) (nrm_binomialSum_le (p := p) a b ha hb)
  calc _ ≤ nrm K (p : Ω) * 1 := mul_le_mul_of_nonneg_left this (nrm_nonneg _)
    _ = _ := mul_one _

theorem nrm_add_pow_prime_pow_sub_le (hp : p.Prime) {a b : Ω} (ha : nrm K a ≤ 1)
    (hb : nrm K b ≤ 1) (k : ℕ) :
    nrm K ((a + b) ^ (p ^ k) - a ^ (p ^ k) - b ^ (p ^ k)) ≤ nrm K (p : Ω) := by
  induction k with
  | zero => simp [nrm_nonneg]
  | succ k ih =>
    set A := a ^ (p ^ k)
    set B := b ^ (p ^ k)
    set X := (a + b) ^ (p ^ k)
    have hA : nrm K A ≤ 1 := nrm_le_one_of_pow ha _
    have hB : nrm K B ≤ 1 := nrm_le_one_of_pow hb _
    have hX : nrm K X ≤ 1 := nrm_le_one_of_pow (nrm_add_le_one ha hb) _
    have e : (a + b) ^ (p ^ (k + 1)) - a ^ (p ^ (k + 1)) - b ^ (p ^ (k + 1)) =
        (X ^ p - (A + B) ^ p) + ((A + B) ^ p - A ^ p - B ^ p) := by
      simp only [X, A, B, pow_succ, pow_mul]; ring
    rw [e]
    refine nrm_add_le_of_le ?_ (nrm_add_pow_prime_sub_le hp hA hB)
    refine (nrm_pow_sub_pow_le hX (nrm_add_le_one hA hB) p).trans ?_
    have : X - (A + B) = X - A - B := by ring
    rw [this]; exact ih

theorem nrm_one_add_pow_sub_one_le (hp : p.Prime) {w : Ω} (hw : nrm K w ≤ 1) {k : ℕ} (hk : k ≠ 0) :
    nrm K ((1 + w) ^ (p ^ k) - 1) ≤ nrm K w * max (nrm K (p : Ω)) (nrm K w ^ (p - 1)) := by
  have hM : max (nrm K (p : Ω)) (nrm K w ^ (p - 1)) ≤ 1 :=
    max_le (nrm_natCast_le_one p) (pow_le_one₀ (nrm_nonneg _) hw)

  have one : ∀ {v : Ω}, nrm K v ≤ 1 →
      nrm K ((1 + v) ^ p - 1) ≤ nrm K v * max (nrm K (p : Ω)) (nrm K v ^ (p - 1)) := by
    intro v hv
    rw [add_pow_prime_eq hp 1 v]
    have e : 1 ^ p + v ^ p + (p : Ω) * 1 * v * ∑ k ∈ Finset.Ioo 0 p, 1 ^ (k - 1) * v ^ (p - k - 1) *
        ((p.choose k / p : ℕ) : Ω) - 1 = v * v ^ (p - 1) + v * ((p : Ω) * ∑ k ∈ Finset.Ioo 0 p,
          1 ^ (k - 1) * v ^ (p - k - 1) * ((p.choose k / p : ℕ) : Ω)) := by
      rw [← pow_succ', Nat.sub_add_cancel hp.one_lt.le]; ring
    rw [e]
    have hS := nrm_binomialSum_le (p := p) (1 : Ω) v (by simp) hv
    refine (nrm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [nrm_mul, nrm_pow]
      exact mul_le_mul_of_nonneg_left (le_max_right _ _) (nrm_nonneg _)
    · rw [nrm_mul, nrm_mul]
      refine mul_le_mul_of_nonneg_left ?_ (nrm_nonneg _)
      calc nrm K (p : Ω) * _ ≤ nrm K (p : Ω) * 1 := mul_le_mul_of_nonneg_left hS (nrm_nonneg _)
        _ ≤ _ := by rw [mul_one]; exact le_max_left _ _
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  induction k with
  | zero => simpa using one hw
  | succ k ih =>
    have hw' := ih (Nat.succ_ne_zero _)
    set w' := (1 + w) ^ (p ^ (k + 1)) - 1
    have hw'1 : nrm K w' ≤ nrm K w := hw'.trans (by
      calc _ ≤ nrm K w * 1 := mul_le_mul_of_nonneg_left hM (nrm_nonneg _)
        _ = _ := mul_one _)
    have e : (1 + w) ^ (p ^ (k + 1 + 1)) = (1 + w') ^ p := by
      simp only [w', pow_succ _ (k + 1), pow_mul]; ring
    rw [e]
    refine (one (hw'1.trans hw)).trans ?_
    have hM' : max (nrm K (p : Ω)) (nrm K w' ^ (p - 1)) ≤ 1 :=
      max_le (nrm_natCast_le_one p) (pow_le_one₀ (nrm_nonneg _) (hw'1.trans hw))
    calc nrm K w' * _ ≤ nrm K w' * 1 := mul_le_mul_of_nonneg_left hM' (nrm_nonneg _)
      _ = nrm K w' := mul_one _
      _ ≤ _ := hw'

end Estimates

section Tower

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (Ω : Type*) [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] (p : ℕ)

structure NormTower where

  E : ℕ → IntermediateField K Ω
  mono : Monotone E
  finiteDimensional : ∀ n, FiniteDimensional K (E n)

  T : ℕ → Finset Gal(Ω/K)
  fix : ∀ n, ∀ σ ∈ T n, ∀ x ∈ E n, σ x = x
  prod_mem : ∀ n, ∀ y ∈ E (n + 1), (∏ σ ∈ T n, σ y) ∈ E n

  k : ℕ → ℕ
  card_alt : ∀ n, (T n).card = p ^ k n
  frequently_ne_zero : ∀ n, ∃ m, n ≤ m ∧ k m ≠ 0

  c : ℝ
  c_nonneg : 0 ≤ c
  c_lt_one : c < 1
  step : ∀ n, ∀ σ ∈ T n, ∀ x ∈ E (n + 1), nrm K (σ x - x) ≤ c * nrm K x
  prime : p.Prime
  nrm_p_lt_one : nrm K (p : Ω) < 1

  value : ℕ → ℝ
  value_pos : ∀ n, 0 < value n
  value_lt_one : ∀ n, value n < 1
  exists_value : ∀ n, ∃ π ∈ E n, nrm K π = value n
  value_zpow : ∀ n, ∀ y ∈ E n, y ≠ 0 → ∃ j : ℤ, nrm K y = value n ^ j
  value_succ : ∀ n, value (n + 1) ^ (p ^ k n) = value n

namespace NormTower

variable {K Ω p} (t : NormTower K Ω p)

def N (n : ℕ) (y : Ω) : Ω :=
  ∏ σ ∈ t.T n, σ y

def ρ : ℝ :=
  max t.c (nrm K (p : Ω))

theorem ρ_nonneg : 0 ≤ t.ρ := le_max_of_le_left t.c_nonneg

theorem ρ_lt_one : t.ρ < 1 := max_lt t.c_lt_one t.nrm_p_lt_one

theorem c_le_ρ : t.c ≤ t.ρ := le_max_left _ _

theorem nrm_p_le_ρ : nrm K (p : Ω) ≤ t.ρ := le_max_right _ _

theorem card_T_pos (n : ℕ) : 0 < (t.T n).card := by
  rw [t.card_alt]; exact pow_pos t.prime.pos _

theorem T_nonempty (n : ℕ) : (t.T n).Nonempty :=
  Finset.card_pos.mp (t.card_T_pos n)

theorem N_mem (n : ℕ) {y : Ω} (hy : y ∈ t.E (n + 1)) : t.N n y ∈ t.E n :=
  t.prod_mem n y hy

theorem N_mul (n : ℕ) (x y : Ω) : t.N n (x * y) = t.N n x * t.N n y := by
  simp only [N, map_mul, Finset.prod_mul_distrib]

@[simp]
theorem N_one (n : ℕ) : t.N n 1 = 1 := by
  simp [N]

@[simp]
theorem N_zero (n : ℕ) : t.N n 0 = 0 := by
  obtain ⟨σ, hσ⟩ := t.T_nonempty n
  simp only [N, map_zero]
  exact Finset.prod_eq_zero hσ rfl

theorem N_pow (n : ℕ) (x : Ω) (m : ℕ) : t.N n (x ^ m) = t.N n x ^ m := by
  simp only [N, map_pow, Finset.prod_pow]

theorem N_inv (n : ℕ) (x : Ω) : t.N n x⁻¹ = (t.N n x)⁻¹ := by
  simp only [N, map_inv₀, Finset.prod_inv_distrib]

theorem nrm_N (n : ℕ) (y : Ω) : nrm K (t.N n y) = nrm K y ^ (p ^ t.k n) := by
  rw [N, nrm_prod, ← t.card_alt n, ← Finset.prod_const]
  exact Finset.prod_congr rfl fun σ _ ↦ nrm_algEquiv σ y

theorem nrm_N_le_one (n : ℕ) {y : Ω} (hy : nrm K y ≤ 1) : nrm K (t.N n y) ≤ 1 := by
  rw [nrm_N]; exact pow_le_one₀ (nrm_nonneg _) hy

theorem N_eq_zero_iff (n : ℕ) {y : Ω} : t.N n y = 0 ↔ y = 0 := by
  rw [← nrm_eq_zero (K := K), nrm_N, pow_eq_zero_iff (pow_pos t.prime.pos _).ne', nrm_eq_zero]

theorem nrm_N_sub_pow_le (n : ℕ) {y : Ω} (hy : y ∈ t.E (n + 1)) (hy1 : nrm K y ≤ 1) :
    nrm K (t.N n y - y ^ (p ^ t.k n)) ≤ t.c := by
  rw [← t.card_alt n, ← Finset.prod_const, N]
  refine nrm_prod_sub_prod_le _ _ _ t.c_nonneg (fun σ _ ↦ by rwa [nrm_algEquiv]) (fun _ _ ↦ hy1)
    fun σ hσ ↦ ?_
  refine (t.step n σ hσ y hy).trans ?_
  calc t.c * nrm K y ≤ t.c * 1 := mul_le_mul_of_nonneg_left hy1 t.c_nonneg
    _ = t.c := mul_one _

theorem nrm_pow_sub_pow_le_ρ {a b : Ω} (ha : nrm K a ≤ 1) (hb : nrm K b ≤ 1)
    (hab : nrm K (a - b) ≤ t.ρ) (m : ℕ) : nrm K (a ^ m - b ^ m) ≤ t.ρ :=
  (nrm_pow_sub_pow_le ha hb m).trans hab

theorem nrm_N_sub_N_le_ρ (n : ℕ) {a b : Ω} (ha : a ∈ t.E (n + 1)) (hb : b ∈ t.E (n + 1))
    (ha1 : nrm K a ≤ 1) (hb1 : nrm K b ≤ 1) (hab : nrm K (a - b) ≤ t.ρ) :
    nrm K (t.N n a - t.N n b) ≤ t.ρ := by
  have e : t.N n a - t.N n b = (t.N n a - a ^ (p ^ t.k n)) + (a ^ (p ^ t.k n) - b ^ (p ^ t.k n)) -
      (t.N n b - b ^ (p ^ t.k n)) := by ring
  rw [e]
  refine nrm_sub_le_of_le (nrm_add_le_of_le ?_ (t.nrm_pow_sub_pow_le_ρ ha1 hb1 hab _)) ?_
  · exact (t.nrm_N_sub_pow_le n ha ha1).trans t.c_le_ρ
  · exact (t.nrm_N_sub_pow_le n hb hb1).trans t.c_le_ρ

theorem nrm_N_add_sub_le_ρ (n : ℕ) {a b : Ω} (ha : a ∈ t.E (n + 1)) (hb : b ∈ t.E (n + 1))
    (ha1 : nrm K a ≤ 1) (hb1 : nrm K b ≤ 1) :
    nrm K (t.N n (a + b) - t.N n a - t.N n b) ≤ t.ρ := by
  set d := p ^ t.k n
  have e : t.N n (a + b) - t.N n a - t.N n b = (t.N n (a + b) - (a + b) ^ d) +
      ((a + b) ^ d - a ^ d - b ^ d) - (t.N n a - a ^ d) - (t.N n b - b ^ d) := by ring
  rw [e]
  refine nrm_sub_le_of_le (nrm_sub_le_of_le (nrm_add_le_of_le ?_ ?_) ?_) ?_
  · exact (t.nrm_N_sub_pow_le n (add_mem ha hb) (nrm_add_le_one ha1 hb1)).trans t.c_le_ρ
  · exact (nrm_add_pow_prime_pow_sub_le t.prime ha1 hb1 _).trans t.nrm_p_le_ρ
  · exact (t.nrm_N_sub_pow_le n ha ha1).trans t.c_le_ρ
  · exact (t.nrm_N_sub_pow_le n hb hb1).trans t.c_le_ρ

theorem nrm_N_sub_N_le_mul (n : ℕ) (hk : t.k n ≠ 0) {a b : Ω} (ha : a ∈ t.E (n + 1))
    (hb : b ∈ t.E (n + 1)) (ha1 : nrm K a ≤ 1) (hb1 : nrm K b ≤ 1) {s : ℝ} (hs : s ≤ t.ρ)
    (hab : nrm K (a - b) ≤ s) : nrm K (t.N n a - t.N n b) ≤ t.ρ * s := by
  have hp1 := t.prime.one_lt
  have hs0 : 0 ≤ s := (nrm_nonneg _).trans hab
  have hρ1 := t.ρ_lt_one
  have hρ0 := t.ρ_nonneg
  set d := p ^ t.k n with hd
  have hdp : p ≤ d := by
    calc p = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ t.k n := Nat.pow_le_pow_right t.prime.pos (Nat.one_le_iff_ne_zero.mpr hk)

  have hsp : s ^ (p - 1) ≤ t.ρ := by
    calc s ^ (p - 1) ≤ t.ρ ^ (p - 1) := pow_le_pow_left₀ hs0 hs _
      _ ≤ t.ρ ^ 1 := pow_le_pow_of_le_one hρ0 hρ1.le (by omega)
      _ = t.ρ := pow_one _

  have main : ∀ {a b : Ω}, a ∈ t.E (n + 1) → b ∈ t.E (n + 1) → nrm K a ≤ 1 → nrm K b ≤ 1 →
      nrm K (a - b) ≤ s → nrm K b ≤ nrm K a → nrm K (t.N n a - t.N n b) ≤ t.ρ * s := by
    intro a b ha hb ha1 hb1 hab hba
    by_cases hsmall : nrm K a ≤ s
    · have hsmallpow : ∀ {x : Ω}, nrm K x ≤ s → nrm K (t.N n x) ≤ t.ρ * s := by
        intro x hx
        rw [nrm_N]
        have hx0 := nrm_nonneg (K := K) x
        calc nrm K x ^ d ≤ s ^ d := pow_le_pow_left₀ hx0 hx _
          _ = s ^ (p - 1) * s ^ (d - (p - 1)) := by rw [← pow_add]; congr 1; omega
          _ ≤ t.ρ * s ^ 1 := by
            refine mul_le_mul hsp (pow_le_pow_of_le_one hs0 (hs.trans hρ1.le) (by omega))
              (pow_nonneg hs0 _) hρ0
          _ = t.ρ * s := by rw [pow_one]
      exact nrm_sub_le_of_le (hsmallpow hsmall) (hsmallpow (hba.trans hsmall))
    · push Not at hsmall
      have ha0 : a ≠ 0 := nrm_pos.mp (hs0.trans_lt hsmall)
      have hna0 : 0 < nrm K a := hs0.trans_lt hsmall
      set w := (b - a) / a with hw
      have hwE : w ∈ t.E (n + 1) := div_mem (sub_mem hb ha) ha
      have hbw : b = a * (1 + w) := by rw [hw]; field_simp; ring
      have hnw : nrm K w * nrm K a = nrm K (b - a) := by
        rw [hw, nrm_div, div_mul_cancel₀ _ hna0.ne']
      have hw1 : nrm K w ≤ 1 := by
        rw [hw, nrm_div, div_le_one hna0, nrm_sub_comm]
        exact hab.trans hsmall.le
      have h1w : nrm K (1 + w) ≤ 1 := nrm_add_le_one (by simp) hw1

      have hN1 : nrm K (t.N n (1 + w) - 1) ≤
          nrm K w * max t.c (max (nrm K (p : Ω)) (nrm K w ^ (p - 1))) := by
        have e : t.N n (1 + w) - 1 = (t.N n (1 + w) - (1 + w) ^ d) + ((1 + w) ^ d - 1) := by ring
        rw [e]
        refine nrm_add_le_of_le ?_ ?_
        · rw [hd, ← t.card_alt n, ← Finset.prod_const, N]
          refine nrm_prod_sub_prod_le _ _ _ (mul_nonneg (nrm_nonneg _) (le_max_of_le_left t.c_nonneg))
            (fun σ _ ↦ by rwa [nrm_algEquiv]) (fun _ _ ↦ h1w) fun σ hσ ↦ ?_
          have : σ (1 + w) - (1 + w) = σ w - w := by rw [map_add, map_one]; ring
          rw [this]
          refine (t.step n σ hσ w hwE).trans ?_
          rw [mul_comm]
          exact mul_le_mul_of_nonneg_left (le_max_left _ _) (nrm_nonneg _)
        · refine (nrm_one_add_pow_sub_one_le t.prime hw1 hk).trans ?_
          exact mul_le_mul_of_nonneg_left (le_max_right _ _) (nrm_nonneg _)
      have hNb : t.N n b - t.N n a = t.N n a * (t.N n (1 + w) - 1) := by
        rw [hbw, t.N_mul]; ring
      rw [← nrm_sub_comm, hNb, nrm_mul, nrm_N]

      have hd1 : nrm K a ^ d = nrm K a ^ (d - 1) * nrm K a := by
        rw [← pow_succ]; congr 1; have := t.prime.pos; omega
      have hM : nrm K a ^ (d - 1) * max t.c (max (nrm K (p : Ω)) (nrm K w ^ (p - 1))) ≤ t.ρ := by
        have hpow : nrm K a ^ (d - 1) ≤ nrm K a ^ (p - 1) :=
          pow_le_pow_of_le_one (nrm_nonneg _) ha1 (by omega)
        have hpow1 : nrm K a ^ (d - 1) ≤ 1 := pow_le_one₀ (nrm_nonneg _) ha1
        have hpow0 : 0 ≤ nrm K a ^ (d - 1) := pow_nonneg (nrm_nonneg _) _
        rcases le_total (max t.c (nrm K (p : Ω))) (nrm K w ^ (p - 1)) with h | h
        · rw [← max_assoc, max_eq_right h]
          calc nrm K a ^ (d - 1) * nrm K w ^ (p - 1) ≤ nrm K a ^ (p - 1) * nrm K w ^ (p - 1) :=
                mul_le_mul_of_nonneg_right hpow (pow_nonneg (nrm_nonneg _) _)
            _ = (nrm K w * nrm K a) ^ (p - 1) := by rw [mul_pow, mul_comm]
            _ ≤ s ^ (p - 1) := by
                rw [hnw, nrm_sub_comm]
                exact pow_le_pow_left₀ (nrm_nonneg _) hab _
            _ ≤ t.ρ := hsp
        · rw [← max_assoc, max_eq_left h]
          calc nrm K a ^ (d - 1) * max t.c (nrm K (p : Ω)) ≤ 1 * t.ρ :=
                mul_le_mul hpow1 le_rfl (le_max_of_le_left t.c_nonneg) zero_le_one
            _ = t.ρ := one_mul _
      calc nrm K a ^ d * nrm K (t.N n (1 + w) - 1)
          ≤ nrm K a ^ d * (nrm K w * max t.c (max (nrm K (p : Ω)) (nrm K w ^ (p - 1)))) :=
            mul_le_mul_of_nonneg_left hN1 (pow_nonneg (nrm_nonneg _) _)
        _ = (nrm K a ^ (d - 1) * max t.c (max (nrm K (p : Ω)) (nrm K w ^ (p - 1)))) *
            (nrm K w * nrm K a) := by rw [hd1]; ring
        _ ≤ t.ρ * s := by
            rw [hnw, nrm_sub_comm]
            exact mul_le_mul hM hab (nrm_nonneg _) hρ0
  rcases le_total (nrm K b) (nrm K a) with h | h
  · exact main ha hb ha1 hb1 hab h
  · rw [nrm_sub_comm]
    exact main hb ha hb1 ha1 (by rwa [nrm_sub_comm]) h

theorem nrm_N_sub_N_le (n : ℕ) {a b : Ω} (ha : a ∈ t.E (n + 1)) (hb : b ∈ t.E (n + 1))
    (ha1 : nrm K a ≤ 1) (hb1 : nrm K b ≤ 1) {s : ℝ} (hs : s ≤ t.ρ) (hab : nrm K (a - b) ≤ s) :
    nrm K (t.N n a - t.N n b) ≤ s := by
  by_cases hk : t.k n = 0
  · obtain ⟨σ, hT⟩ : ∃ σ, t.T n = {σ} := Finset.card_eq_one.mp (by rw [t.card_alt, hk, pow_zero])
    simp only [N, hT, Finset.prod_singleton]
    rw [← map_sub, nrm_algEquiv]; exact hab
  · refine (t.nrm_N_sub_N_le_mul n hk ha hb ha1 hb1 hs hab).trans ?_
    have hs0 : 0 ≤ s := (nrm_nonneg _).trans hab
    calc t.ρ * s ≤ 1 * s := mul_le_mul_of_nonneg_right t.ρ_lt_one.le hs0
      _ = s := one_mul s

end NormTower

end Tower

end GroundTheory.PAdicHodge
