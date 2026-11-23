import Mathlib

namespace GlobalTheory.RealAlgebraCharacters

open Filter Topology

section
variable {X : Type} {B : Type} [AddCommGroup B] (χ : B → X → ℂ)

theorem span_mul (hadd : ∀ (a b : B) (x : X), χ (a + b) x = χ a x * χ b x)
    {f g : X → ℂ} (hf : f ∈ Submodule.span ℂ (Set.range χ))
    (hg : g ∈ Submodule.span ℂ (Set.range χ)) : f * g ∈ Submodule.span ℂ (Set.range χ) := by
  induction hf using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨a, rfl⟩ := hu
    induction hg using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨b, rfl⟩ := hv
      exact Submodule.subset_span ⟨a + b, funext fun x => hadd a b x⟩
    | zero => simp
    | add v w _ _ hv hw =>
      rw [mul_add]
      exact Submodule.add_mem _ hv hw
    | smul c v _ hv =>
      rw [mul_smul_comm]
      exact Submodule.smul_mem _ c hv
  | zero => simp
  | add u w _ _ hu hw =>
    rw [add_mul]
    exact Submodule.add_mem _ hu hw
  | smul c u _ hu =>
    rw [smul_mul_assoc]
    exact Submodule.smul_mem _ c hu

omit [AddCommGroup B] in

theorem span_bdd (hn : ∀ (a : B) (x : X), ‖χ a x‖ = 1)
    {f : X → ℂ} (hf : f ∈ Submodule.span ℂ (Set.range χ)) : ∃ M : ℝ, ∀ x, ‖f x‖ ≤ M := by
  induction hf using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨a, rfl⟩ := hu
    exact ⟨1, fun x => (hn a x).le⟩
  | zero => exact ⟨0, fun x => by simp⟩
  | add u w _ _ hu hw =>
    obtain ⟨M1, h1⟩ := hu
    obtain ⟨M2, h2⟩ := hw
    refine ⟨M1 + M2, fun x => ?_⟩
    show ‖u x + w x‖ ≤ M1 + M2
    exact (norm_add_le _ _).trans (add_le_add (h1 x) (h2 x))
  | smul c u _ hu =>
    obtain ⟨M, h⟩ := hu
    refine ⟨‖c‖ * M, fun x => ?_⟩
    show ‖c • u x‖ ≤ ‖c‖ * M
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (h x) (norm_nonneg _)

theorem chi_neg (hadd : ∀ (a b : B) (x : X), χ (a + b) x = χ a x * χ b x)
    (h0 : ∀ x, χ 0 x = 1) (hn : ∀ (a : B) (x : X), ‖χ a x‖ = 1) (b : B) (x : X) :
    χ (-b) x = (starRingEnd ℂ) (χ b x) := by
  have h1 : χ (-b) x * χ b x = 1 := by rw [← hadd, neg_add_cancel, h0]
  have h2 : χ (-b) x = (χ b x)⁻¹ := eq_inv_of_mul_eq_one_left h1
  rw [h2, Complex.inv_def, Complex.normSq_eq_norm_sq, hn b x]
  simp

def realAlg [TopologicalSpace X] (hadd : ∀ (a b : B) (x : X), χ (a + b) x = χ a x * χ b x)
    (h0 : ∀ x, χ 0 x = 1) : Subalgebra ℝ C(X, ℝ) where
  carrier := {f | (fun x => ((f x : ℝ) : ℂ)) ∈ Submodule.span ℂ (Set.range χ)}
  mul_mem' := by
    intro f g hf hg
    have := span_mul χ hadd hf hg
    show (fun x => (((f * g) x : ℝ) : ℂ)) ∈ Submodule.span ℂ (Set.range χ)
    convert this using 1
    funext x
    simp
  add_mem' := by
    intro f g hf hg
    have := (Submodule.span ℂ (Set.range χ)).add_mem hf hg
    show (fun x => (((f + g) x : ℝ) : ℂ)) ∈ Submodule.span ℂ (Set.range χ)
    convert this using 1
    funext x
    simp
  algebraMap_mem' := by
    intro r
    have h : χ 0 ∈ Submodule.span ℂ (Set.range χ) := Submodule.subset_span ⟨0, rfl⟩
    have := Submodule.smul_mem _ (r : ℂ) h
    show (fun x => (((algebraMap ℝ C(X, ℝ) r) x : ℝ) : ℂ)) ∈ Submodule.span ℂ (Set.range χ)
    convert this using 1
    funext x
    simp [h0]

theorem realAlg_sep [TopologicalSpace X] (hc : ∀ b, Continuous (χ b))
    (hadd : ∀ (a b : B) (x : X), χ (a + b) x = χ a x * χ b x)
    (h0 : ∀ x, χ 0 x = 1) (hn : ∀ (a : B) (x : X), ‖χ a x‖ = 1)
    (hs : ∀ x y : X, x ≠ y → ∃ b, χ b x ≠ χ b y) : (realAlg χ hadd h0).SeparatesPoints := by
  intro x y hxy
  obtain ⟨b, hb⟩ := hs x y hxy
  have hneg : ∀ u, χ (-b) u = (starRingEnd ℂ) (χ b u) := fun u => chi_neg χ hadd h0 hn b u
  let fre : C(X, ℝ) := ⟨fun u => (χ b u).re, Complex.continuous_re.comp (hc b)⟩
  let fim : C(X, ℝ) := ⟨fun u => (χ b u).im, Complex.continuous_im.comp (hc b)⟩
  have hre : fre ∈ realAlg χ hadd h0 := by
    show (fun u => (((χ b u).re : ℝ) : ℂ)) ∈ Submodule.span ℂ (Set.range χ)
    have he : (fun u => (((χ b u).re : ℝ) : ℂ)) = (1 / 2 : ℂ) • (χ b + χ (-b)) := by
      funext u
      simp only [Pi.smul_apply, Pi.add_apply, hneg, smul_eq_mul]
      rw [Complex.re_eq_add_conj]
      ring
    rw [he]
    exact Submodule.smul_mem _ _ (Submodule.add_mem _ (Submodule.subset_span ⟨b, rfl⟩)
      (Submodule.subset_span ⟨-b, rfl⟩))
  have him : fim ∈ realAlg χ hadd h0 := by
    show (fun u => (((χ b u).im : ℝ) : ℂ)) ∈ Submodule.span ℂ (Set.range χ)
    have he : (fun u => (((χ b u).im : ℝ) : ℂ)) = (1 / (2 * Complex.I)) • (χ b - χ (-b)) := by
      funext u
      simp only [Pi.smul_apply, Pi.sub_apply, hneg, smul_eq_mul]
      rw [Complex.im_eq_sub_conj]
      ring
    rw [he]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (Submodule.subset_span ⟨b, rfl⟩)
      (Submodule.subset_span ⟨-b, rfl⟩))
  by_cases hr : (χ b x).re = (χ b y).re
  · refine ⟨fim, ⟨fim, him, rfl⟩, fun heq => hb (Complex.ext hr heq)⟩
  · exact ⟨fre, ⟨fre, hre, rfl⟩, hr⟩

theorem step [TopologicalSpace X] (hc : ∀ b, Continuous (χ b))
    (hadd : ∀ (a b : B) (x : X), χ (a + b) x = χ a x * χ b x)
    (h0 : ∀ x, χ 0 x = 1) (hn : ∀ (a : B) (x : X), ‖χ a x‖ = 1)
    (hs : ∀ x y : X, x ≠ y → ∃ b, χ b x ≠ χ b y) (β : X → ℝ) (hβ : Continuous β)
    (hβ1 : ∀ u, 0 ≤ β u ∧ β u ≤ 1) {K : Set X} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) :
    ∃ (s : Finset B) (c : B → ℂ), (∀ x, ‖∑ b ∈ s, c b * χ b x‖ ≤ 2) ∧
      ∀ x ∈ K, ‖∑ b ∈ s, c b * χ b x - (β x : ℂ)‖ ≤ 2 * ε := by
  obtain ⟨g, hgA, hg⟩ :=
    ContinuousMap.exists_mem_subalgebra_near_continuous_of_isCompact_of_separatesPoints
      (realAlg_sep χ hc hadd h0 hn hs) ⟨β, hβ⟩ hK hε
  obtain ⟨M, hM⟩ := span_bdd χ hn hgA
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn (-M) M (fun t => max 0 (min t 1))
    (by fun_prop) ε hε
  have hmem : Polynomial.aeval g p ∈ realAlg χ hadd h0 := by
    have : Algebra.adjoin ℝ {g} ≤ realAlg χ hadd h0 :=
      Algebra.adjoin_le (Set.singleton_subset_iff.2 hgA)
    exact this (Polynomial.aeval_mem_adjoin_singleton ℝ g)
  have hmem' : (fun x => (((Polynomial.aeval g p) x : ℝ) : ℂ)) ∈
      Submodule.span ℂ (Set.range χ) := hmem
  obtain ⟨c, hcf⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hmem'
  have hval : ∀ x, ∑ b ∈ c.support, c b * χ b x = ((p.eval (g x) : ℝ) : ℂ) := by
    intro x
    have := congrFun hcf x
    rw [Polynomial.aeval_continuousMap_apply] at this
    rw [← this, Finsupp.sum, Finset.sum_apply]
    simp
  have hnear : ∀ x, |p.eval (g x) - max 0 (min (g x) 1)| < ε := by
    intro x
    have := hM x
    rw [Complex.norm_real, Real.norm_eq_abs] at this
    exact hp _ (abs_le.1 this)
  refine ⟨c.support, c, fun x => ?_, fun x hx => ?_⟩
  · rw [hval, Complex.norm_real, Real.norm_eq_abs]
    have h1 := abs_lt.1 (hnear x)
    have h2 : 0 ≤ max 0 (min (g x) 1) := le_max_left _ _
    have h3 : max 0 (min (g x) 1) ≤ 1 := max_le zero_le_one (min_le_right _ _)
    rw [abs_le]
    constructor <;> linarith [h1.1, h1.2]
  · rw [hval, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have h1 := abs_lt.1 (hnear x)
    have h2 : |g x - β x| < ε := hg x hx
    have h3 := abs_lt.1 h2
    have h4 := hβ1 x
    have h5 : max 0 (min (g x) 1) ≤ β x + ε :=
      max_le (by linarith [h4.1]) ((min_le_left _ _).trans (by linarith [h3.2]))
    have h6 : β x - ε ≤ max 0 (min (g x) 1) :=
      le_max_of_le_right (le_min (by linarith [h3.1]) (by linarith [h4.2]))
    rw [abs_le]
    constructor <;> linarith [h1.1, h1.2]

end

theorem main {X : Type} [PseudoMetricSpace X] [ProperSpace X] (x₀ : X) {B : Type}
    [AddCommGroup B] (χ : B → X → ℂ) (hc : ∀ b, Continuous (χ b))
    (hadd : ∀ (a b : B) (x : X), χ (a + b) x = χ a x * χ b x)
    (h0 : ∀ x, χ 0 x = 1) (hn : ∀ (a : B) (x : X), ‖χ a x‖ = 1)
    (hs : ∀ x y : X, x ≠ y → ∃ b, χ b x ≠ χ b y) (β : X → ℝ) (hβ : Continuous β)
    (hβ1 : ∀ u, 0 ≤ β u ∧ β u ≤ 1) :
    ∃ (s : ℕ → Finset B) (c : ℕ → B → ℂ),
      (∀ (n : ℕ) (x : X), ‖∑ b ∈ s n, c n b * χ b x‖ ≤ 2) ∧
      ∀ x : X, Tendsto (fun n : ℕ => ∑ b ∈ s n, c n b * χ b x) atTop (𝓝 (β x : ℂ)) := by
  have key : ∀ n : ℕ, ∃ (s : Finset B) (c : B → ℂ), (∀ x, ‖∑ b ∈ s, c b * χ b x‖ ≤ 2) ∧
      ∀ x ∈ Metric.closedBall x₀ (n : ℝ),
        ‖∑ b ∈ s, c b * χ b x - (β x : ℂ)‖ ≤ 2 * (1 / ((n : ℝ) + 1)) := by
    intro n
    refine step χ hc hadd h0 hn hs β hβ hβ1 (isCompact_closedBall x₀ n)
      Nat.one_div_pos_of_nat ?_
    rw [div_le_one (by positivity)]
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  choose s c h1 h2 using key
  refine ⟨s, c, h1, fun x => ?_⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun n : ℕ => 2 * (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2
  refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_ hlim
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (dist x x₀)]
    with n hn'
  exact h2 n x hn'

end GlobalTheory.RealAlgebraCharacters
