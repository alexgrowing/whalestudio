import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open ReciprocityTheory.ChartRestriction.G.Geo

section Sat

variable {Ω : Type*} [Field Ω] {E : Type*} [AddCommGroup E] [Module Ω E]
variable {S : Type*} [SetLike S Ω] [SubringClass S Ω]

theorem inv_pow_smul_mem (Y : AddSubgroup E) {u : Ω} (hYu : ∀ e ∈ Y, u⁻¹ • e ∈ Y) (k : ℕ) :
    ∀ e ∈ Y, (u⁻¹) ^ k • e ∈ Y := by
  induction k with
  | zero => intro e he; simpa using he
  | succ k ih => intro e he; rw [pow_succ, mul_smul]; exact ih _ (hYu e he)

theorem exists_pow_smul_mem_iff_of_loc (A : S) (X Y : AddSubgroup E) {u f : Ω} (j : ℕ)
    (hu0 : u ≠ 0) (huA : u ∈ A) (hg : u ^ j * f ∈ A) (hXA : ∀ a ∈ A, ∀ e ∈ X, a • e ∈ X)
    (hXY : X ≤ Y) (hYu : ∀ e ∈ Y, u⁻¹ • e ∈ Y) (hYX : ∀ e ∈ Y, ∃ k : ℕ, u ^ k • e ∈ X) (e : E) :
    (∃ n : ℕ, (u ^ (j + 1) * f) ^ n • e ∈ X) ↔ ∃ n : ℕ, f ^ n • e ∈ Y := by
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have h1 : f ^ n • e = ((u⁻¹) ^ ((j + 1) * n)) • ((u ^ (j + 1) * f) ^ n • e) := by
      rw [smul_smul]
      congr 1
      rw [mul_pow, ← pow_mul, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hu0, one_pow, one_mul]
    rw [h1]
    exact inv_pow_smul_mem Y hYu _ _ (hXY hn)
  · rintro ⟨n, hn⟩
    obtain ⟨k, hk⟩ := hYX _ hn
    refine ⟨n + k, ?_⟩
    have h1 : (u ^ (j + 1) * f) ^ (n + k) • e =
        ((u ^ j * f) ^ k * u ^ ((j + 1) * n)) • (u ^ k • f ^ n • e) := by
      rw [smul_smul, smul_smul]
      congr 1
      ring
    rw [h1]
    exact hXA _ (mul_mem (pow_mem hg _) (pow_mem huA _)) _ hk

theorem exists_sum_mul_pow_eq_one (A : S) {k : ℕ} (f c : Fin k → Ω) (hf : ∀ l, f l ∈ A)
    (hc : ∀ l, c l ∈ A) (h1 : ∑ l, c l * f l = 1) (N : ℕ) :
    ∃ d : Fin k → Ω, (∀ l, d l ∈ A) ∧ ∑ l, d l * f l ^ N = 1 := by
  let f' : Fin k → A := fun l => ⟨f l, hf l⟩
  have hspan : Ideal.span (Set.range f') = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    have : (1 : A) = ∑ l, (⟨c l, hc l⟩ : A) * f' l := Subtype.ext (by simp [f', h1])
    rw [this]
    exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨l, rfl⟩)
  have hpow := Ideal.span_pow_eq_top _ hspan N
  rw [← Set.range_comp] at hpow
  have h1' : (1 : A) ∈ Ideal.span (Set.range ((fun y => y ^ N) ∘ f')) := by
    rw [hpow]; exact Submodule.mem_top
  obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun A).1 h1'
  refine ⟨fun l => d l, fun l => (d l).2, ?_⟩
  have := congrArg Subtype.val hd
  simpa [f'] using this

theorem exists_uniform_mul (T : Submonoid ℤ) (A : S) (L : AddSubgroup E)
    (hLA : ∀ a ∈ A, ∀ e ∈ L, a • e ∈ L) {ζ : Ω} (hζ : ζ ∈ A) {ι : Type*} [Fintype ι] (w : ι → E)
    (h : ∀ l, ∃ t ∈ T, ∃ n : ℕ, ((t : Ω) * ζ ^ n) • w l ∈ L) :
    ∃ t ∈ T, ∃ n : ℕ, ∀ l, ∀ n' ≥ n, ((t : Ω) * ζ ^ n') • w l ∈ L := by
  classical
  choose t ht n hn using h
  refine ⟨∏ l, t l, prod_mem fun l _ => ht l, Finset.univ.sup n, fun l n' hn' => ?_⟩
  have hle : n l ≤ n' := le_trans (Finset.le_sup (Finset.mem_univ l)) hn'
  have : (((∏ l, t l : ℤ) : Ω) * ζ ^ n') =
      (((∏ l' ∈ Finset.univ.erase l, t l' : ℤ) : Ω) * ζ ^ (n' - n l)) * ((t l : Ω) * ζ ^ n l) := by
    rw [← Finset.mul_prod_erase Finset.univ t (Finset.mem_univ l), Int.cast_mul,
      ← pow_sub_mul_pow ζ hle]
    ring
  rw [this, mul_smul]
  exact hLA _ (mul_mem (intCast_mem A _) (pow_mem hζ _)) _ (hn l)

end Sat

section Gens

variable {Ω : Type*} [Field Ω] {E : Type*} [AddCommGroup E] [Module Ω E]
variable {R : Type*} [CommRing R] [Algebra R Ω] {τ : Type*} {x : τ → Ω} {r : ℕ}

theorem chartBundle_pow_smul_mem (B : ChartBundle R x r E) {i : τ} {a : Ω}
    (ha : a ∈ chartRing R x i) (m : ℕ) {e : E} (he : e ∈ B.lat i) : a ^ m • e ∈ B.lat i :=
  B.stable i _ (pow_mem ha m) e he

theorem chartBundle_exists_gens (B : ChartBundle R x r E) {i : τ} (hi : x i ≠ 0) :
    ∃ (k : ℕ) (G : Fin k × Fin r → E), (∀ j, G j ∈ B.lat i) ∧
      ∀ e ∈ B.lat i, ∃ β : Fin k × Fin r → Ω, (∀ j, β j ∈ chartRing R x i) ∧
        e = ∑ j, β j • G j := by
  classical
  obtain ⟨k, f, c, hf, hc, hsum, hb⟩ := B.frame i hi
  choose b _ _ hiff using hb
  have hbsat : ∀ l q, ∃ n : ℕ, f l ^ n • b l q ∈ B.lat i := by
    intro l q
    refine (hiff l (b l q)).2 ⟨Pi.single q 1, fun q' => ⟨0, ?_⟩, by simp [Pi.single_apply]⟩
    rw [pow_zero, one_mul]
    by_cases h : q' = q
    · subst h; simp only [Pi.single_eq_same]; exact one_mem _
    · rw [Pi.single_eq_of_ne h]; exact zero_mem _
  choose n hn using hbsat
  set n₀ := Finset.univ.sup fun lq : Fin k × Fin r => n lq.1 lq.2 with hn₀
  have hle : ∀ l q, n l q ≤ n₀ := fun l q =>
    Finset.le_sup (f := fun lq : Fin k × Fin r => n lq.1 lq.2) (Finset.mem_univ (l, q))
  refine ⟨k, fun lq => f lq.1 ^ n₀ • b lq.1 lq.2, fun lq => ?_, fun e he => ?_⟩
  · have : f lq.1 ^ n₀ • b lq.1 lq.2 = f lq.1 ^ (n₀ - n lq.1 lq.2) • f lq.1 ^ n lq.1 lq.2 • b lq.1 lq.2 := by
      rw [smul_smul, pow_sub_mul_pow _ (hle _ _)]
    show f lq.1 ^ n₀ • b lq.1 lq.2 ∈ B.lat i
    rw [this]
    exact chartBundle_pow_smul_mem B (hf _) _ (hn _ _)
  · have hco : ∀ l, ∃ a : Fin r → Ω, (∀ q, ∃ n : ℕ, f l ^ n * a q ∈ chartRing R x i) ∧
        e = ∑ q, a q • b l q := fun l => (hiff l e).1 ⟨0, by simpa using he⟩
    choose a ha he' using hco
    choose m hm using ha
    set M := Finset.univ.sup fun lq : Fin k × Fin r => m lq.1 lq.2 with hM
    have hleM : ∀ l q, m l q ≤ M := fun l q =>
      Finset.le_sup (f := fun lq : Fin k × Fin r => m lq.1 lq.2) (Finset.mem_univ (l, q))
    have hfa : ∀ l q, f l ^ M * a l q ∈ chartRing R x i := fun l q => by
      rw [← pow_sub_mul_pow _ (hleM l q), mul_assoc]
      exact mul_mem (pow_mem (hf l) _) (hm l q)
    obtain ⟨d, hd, hd1⟩ := exists_sum_mul_pow_eq_one (chartRing R x i) f c hf hc hsum (M + n₀)
    refine ⟨fun lq => d lq.1 * (f lq.1 ^ M * a lq.1 lq.2), fun lq => mul_mem (hd _) (hfa _ _), ?_⟩
    rw [Fintype.sum_prod_type]
    calc e = (∑ l, d l * f l ^ (M + n₀)) • e := by rw [hd1, one_smul]
      _ = ∑ l, d l • (f l ^ (M + n₀) • e) := by
        rw [Finset.sum_smul]; exact Finset.sum_congr rfl fun l _ => by rw [mul_smul]
      _ = ∑ l, ∑ q, (d l * (f l ^ M * a l q)) • f l ^ n₀ • b l q := by
        refine Finset.sum_congr rfl fun l _ => ?_
        conv_lhs => rw [he' l]
        rw [Finset.smul_sum, Finset.smul_sum]
        refine Finset.sum_congr rfl fun q _ => ?_
        simp only [smul_smul]
        congr 1
        ring

end Gens

end GroundTheory.Heights₂.Heights.Model
