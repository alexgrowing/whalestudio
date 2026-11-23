import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPos
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.HilbertQExpPadicBoundAlgebraProperties

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.QPow

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {p : ℕ} [Fact p.Prime] {ι : Qbar p ≃+* ℂ}

theorem norm_p (ι : Qbar p ≃+* ℂ) : ‖ι.symm (p : ℂ)‖ = (p : ℝ)⁻¹ := by
  rw [map_natCast]
  have h : ‖(algebraMap ℚ_[p] (PadicAlgCl p) (p : ℚ_[p]))‖ = ‖(p : ℚ_[p])‖ :=
    PadicAlgCl.norm_extends p _
  rw [map_natCast, Padic.norm_p] at h
  exact h

private theorem hasQ_const (c : ℂ) :
    HasQ (F := F) (fun _ : Hn F => c) (({0} : Set F).indicator fun _ => c) := by
  classical
  refine ⟨⟨1, one_pos, fun ξ hξ => ?_⟩, fun z => ?_⟩
  · have h0 : ξ = 0 := by
      by_contra hne
      exact hξ (by simp [Set.indicator_apply, hne])
    subst h0
    refine ⟨Or.inl rfl, ?_⟩
    rw [mul_zero]
    exact isIntegral_zero
  · have h := hasSum_single
      (f := fun ξ : F => (({0} : Set F).indicator (fun _ => c) ξ) * ez ξ z) 0
      (fun b hb => by simp [Set.indicator_apply, hb])
    convert h using 1
    simp [Set.indicator_apply, ez, reAt]

theorem small_const {r : ℝ} {g : Hn F → ℂ} (h : Small ι r g) (c : ℂ) :
    Small (F := F) ι ‖ι.symm c‖ (fun _ : Hn F => c) := by
  classical
  refine ⟨_, hasQ_const c, fun ξ => ?_⟩
  by_cases hξ : ξ = 0
  · simp [Set.indicator_apply, hξ]
  · simp [Set.indicator_apply, hξ]

theorem small_mono {r s : ℝ} {g : Hn F → ℂ} (h : Small ι r g) (hrs : r ≤ s) : Small ι s g := by
  obtain ⟨a, ha, hb⟩ := h
  exact ⟨a, ha, fun ξ => (hb ξ).trans hrs⟩

private theorem hasQ_add {f g : Hn F → ℂ} {a b : F → ℂ} (hf : HasQ f a) (hg : HasQ g b) :
    HasQ (f + g) (a + b) := by
  obtain ⟨⟨D, hD, hDa⟩, ha⟩ := hf
  obtain ⟨⟨E, hE, hEb⟩, hb⟩ := hg
  refine ⟨⟨D * E, Nat.mul_pos hD hE, fun ξ hξ => ?_⟩, fun z => ?_⟩
  · by_cases h0 : a ξ = 0
    · have hb0 : b ξ ≠ 0 := by
        intro hb0
        apply hξ
        simp [h0, hb0]
      obtain ⟨h1, h2⟩ := hEb ξ hb0
      refine ⟨h1, ?_⟩
      have h3 := (isIntegral_natCast (R := ℤ) (B := F) D).mul h2
      have e : ((D * E : ℕ) : F) * ξ = (D : F) * ((E : F) * ξ) := by
        push_cast
        ring
      rw [e]
      exact h3
    · obtain ⟨h1, h2⟩ := hDa ξ h0
      refine ⟨h1, ?_⟩
      have h3 := (isIntegral_natCast (R := ℤ) (B := F) E).mul h2
      have e : ((D * E : ℕ) : F) * ξ = (E : F) * ((D : F) * ξ) := by
        push_cast
        ring
      rw [e]
      exact h3
  · have h := (ha z).add (hb z)
    simp only [Pi.add_apply, add_mul]
    exact h

theorem small_add {r s : ℝ} {f g : Hn F → ℂ} (hf : Small ι r f) (hg : Small ι s g) : Small ι (max r s) (f + g) := by
  obtain ⟨a, ha, ha'⟩ := hf
  obtain ⟨b, hb, hb'⟩ := hg
  refine ⟨a + b, hasQ_add ha hb, fun ξ => ?_⟩
  rw [Pi.add_apply, map_add]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max (ha' ξ) (hb' ξ))

theorem small_mul {r s : ℝ} {f g : Hn F → ℂ} (hf : Small ι r f) (hg : Small ι s g) : Small ι (r * s) (f * g) := by
  obtain ⟨a, ha, ha'⟩ := hf
  obtain ⟨b, hb, hb'⟩ := hg
  have hr : 0 ≤ r := (norm_nonneg _).trans (ha' 0)
  have hs : 0 ≤ s := (norm_nonneg _).trans (hb' 0)
  obtain ⟨c, hc, hc'⟩ := hasQ_mul F f g a b ha hb
  refine ⟨c, hc, fun ξ => ?_⟩
  obtain ⟨t, ht⟩ := hc' ξ
  rw [ht, map_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg hr hs) fun η _ => ?_
  rw [map_mul, norm_mul]
  exact mul_le_mul (ha' η) (hb' (ξ - η)) (norm_nonneg _) hr

theorem small_nonneg {r : ℝ} {f : Hn F → ℂ} (hf : Small ι r f) : 0 ≤ r := by
  obtain ⟨a, -, hb⟩ := hf
  exact (norm_nonneg _).trans (hb 0)

theorem small_zero {r : ℝ} {f : Hn F → ℂ} (hf : Small ι r f) : Small ι r (0 : Hn F → ℂ) := by
  refine ⟨0, ⟨⟨1, one_pos, fun ξ hξ => (hξ rfl).elim⟩, fun z => ?_⟩, fun ξ => ?_⟩
  · simpa using (hasSum_zero : HasSum (fun _ : F => (0 : ℂ)) 0)
  · simpa using small_nonneg hf

theorem pow_sub_one {r : ℝ} {f : Hn F → ℂ} (h : Small ι r (f - 1)) (hr : r ≤ 1) :
    ∀ m : ℕ, Small ι r (f ^ m - 1) := by
  have hr0 := small_nonneg h
  intro m
  induction m with
  | zero => simpa using small_zero h
  | succ m ih =>
    have e : f ^ (m + 1) - 1 = (f ^ m - 1) * (f - 1) + ((f ^ m - 1) + (f - 1)) := by ring
    rw [e]
    have h1 := small_add (small_mul ih h) (small_add ih h)
    refine small_mono h1 ?_
    rw [max_self]
    exact max_le (mul_le_of_le_one_left hr0 hr) le_rfl

theorem sum_small {r : ℝ} {f : Hn F → ℂ} (h : Small ι r (f - 1)) (hr : r ≤ (p : ℝ)⁻¹) :
    ∀ n : ℕ, Small ι (p : ℝ)⁻¹ (∑ i ∈ Finset.range n, (f ^ i - 1)) := by
  have hp1 : (p : ℝ)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt.le)
  have hs : Small ι (p : ℝ)⁻¹ (f - 1) := small_mono h hr
  intro n
  induction n with
  | zero => simpa using small_zero hs
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have h1 := small_add ih (pow_sub_one hs hp1 n)
    rwa [max_self] at h1

theorem pow_p {r : ℝ} {f : Hn F → ℂ} (h : Small ι r (f - 1)) (hr : r ≤ (p : ℝ)⁻¹) :
    Small ι (r * (p : ℝ)⁻¹) (f ^ p - 1) := by
  have key : ∀ x : ℂ, x ^ p - 1 =
      (x - 1) * ∑ i ∈ Finset.range p, (x ^ i - 1) + (p : ℂ) * (x - 1) := by
    intro x
    have hg := geom_sum_mul x p
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    linear_combination (-1 : ℂ) * hg
  have e : f ^ p - 1 = (f - 1) * ∑ i ∈ Finset.range p, (f ^ i - 1) +
      (fun _ : Hn F => (p : ℂ)) * (f - 1) := by
    funext z
    simp only [Pi.sub_apply, Pi.pow_apply, Pi.one_apply, Pi.mul_apply, Pi.add_apply,
      Finset.sum_apply]
    exact key (f z)
  rw [e]
  have h1 := small_mul h (sum_small h hr p)
  have h2 := small_mul (small_const h (p : ℂ)) h
  rw [norm_p ι] at h2
  refine small_mono (small_add h1 h2) ?_
  rw [mul_comm (p : ℝ)⁻¹ r, max_self]

theorem main : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (p : ℕ) [Fact p.Prime] (ι : Qbar p ≃+* ℂ)
    (f : Hn F → ℂ), Small ι (p : ℝ)⁻¹ (f - 1) → ∀ N m : ℕ,
      Small ι ((p : ℝ)⁻¹ ^ (N + 1)) (f ^ (p ^ N * m) - 1) := by
  intro F _ _ _ p _ ι f h N m
  have hp0 : (0 : ℝ) ≤ (p : ℝ)⁻¹ := by positivity
  have hp1 : (p : ℝ)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt.le)
  have step : ∀ n : ℕ, Small ι ((p : ℝ)⁻¹ ^ (n + 1)) (f ^ (p ^ n) - 1) := by
    intro n
    induction n with
    | zero => simpa using h
    | succ n ih =>
      have h1 := pow_p ih (pow_le_of_le_one hp0 hp1 (Nat.succ_ne_zero n))
      rw [← pow_mul, ← pow_succ, ← pow_succ] at h1
      exact h1
  have h2 := pow_sub_one (step N) (pow_le_one₀ hp0 hp1) m
  rwa [← pow_mul] at h2

end GlobalTheory.QPow

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbertQExp_padicCongruence_pow_prime_pow : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (p : ℕ) [Fact p.Prime] (ι : Qbar p ≃+* ℂ) (f : Hn F → ℂ), Small ι (p : ℝ)⁻¹ (f - 1) → ∀ N m : ℕ, Small ι ((p : ℝ)⁻¹ ^ (N + 1)) (f ^ (p ^ N * m) - 1) := by
  first | exact @GlobalTheory.QPow.main | exact GlobalTheory.QPow.main | (intros; apply GlobalTheory.QPow.main <;> assumption)
