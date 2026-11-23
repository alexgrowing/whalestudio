import Mathlib
import GroundTheory.GlobalFields.TateThesis.HeckeLFunction

open NumberField Ideal Complex Filter Topology

namespace GroundTheory.Global

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

theorem finite_setOf_le_of_ne_bot {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) :
    {J : Ideal (𝓞 K) | I ≤ J}.Finite := by
  have hN : absNorm I ≠ 0 := fun h ↦ hI (absNorm_eq_zero_iff.1 h)
  refine (Set.Finite.biUnion (Finset.finite_toSet (Finset.range (absNorm I + 1)))
    fun k _ ↦ Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 K) k).subset fun J hJ ↦ ?_
  simp only [Set.mem_iUnion, Finset.coe_range, Set.mem_Iio]
  exact ⟨absNorm J, Nat.lt_succ_of_le (Nat.le_of_dvd (Nat.pos_of_ne_zero hN)
    (absNorm_dvd_absNorm_of_le hJ)), rfl⟩

def idealDivisors (I : Ideal (𝓞 K)) : Finset (Ideal (𝓞 K)) :=
  if hI : I = ⊥ then ∅ else (finite_setOf_le_of_ne_bot hI).toFinset

theorem mem_idealDivisors {I J : Ideal (𝓞 K)} (hI : I ≠ ⊥) : J ∈ idealDivisors I ↔ I ≤ J := by
  rw [idealDivisors, dif_neg hI, Set.Finite.mem_toFinset]
  rfl

@[simp]
theorem idealDivisors_bot : idealDivisors (⊥ : Ideal (𝓞 K)) = ∅ :=
  dif_pos rfl

def divisorSum (ψ : Ideal (𝓞 K) → ℝ) (I : Ideal (𝓞 K)) : ℝ :=
  ∑ J ∈ idealDivisors I, ψ J

@[simp]
theorem divisorSum_bot (ψ : Ideal (𝓞 K) → ℝ) : divisorSum ψ ⊥ = 0 := by
  rw [divisorSum, idealDivisors_bot, Finset.sum_empty]

theorem divisorSum_top (ψ : Ideal (𝓞 K) → ℝ) : divisorSum ψ ⊤ = ψ ⊤ := by
  have h : idealDivisors (⊤ : Ideal (𝓞 K)) = {⊤} := by
    ext J
    rw [mem_idealDivisors top_ne_bot, Finset.mem_singleton, top_le_iff]
  rw [divisorSum, h, Finset.sum_singleton]

theorem mul_sup_eq_of_le {R : Type*} [CommRing R] {I J B₁ B₂ : Ideal R} (hIJ : I ⊔ J = ⊤)
    (h₁ : I ≤ B₁) (h₂ : J ≤ B₂) : B₁ * B₂ ⊔ I = B₁ := by
  have hB₂ : B₂ ⊔ I = ⊤ := top_le_iff.1 (hIJ ▸ sup_le (le_sup_of_le_right le_rfl)
    (le_sup_of_le_left h₂))
  refine le_antisymm (sup_le Ideal.mul_le_left h₁) ?_
  calc B₁ = B₁ * (B₂ ⊔ I) := by rw [hB₂, Ideal.mul_top]
    _ = B₁ * B₂ ⊔ B₁ * I := Ideal.mul_sup _ _ _
    _ ≤ B₁ * B₂ ⊔ I := sup_le_sup_left Ideal.mul_le_right _

theorem sup_mul_sup_eq_of_le {R : Type*} [CommRing R] {I J D : Ideal R} (hIJ : I ⊔ J = ⊤)
    (hD : I * J ≤ D) : (D ⊔ I) * (D ⊔ J) = D := by
  refine le_antisymm ?_ ?_
  · rw [Ideal.sup_mul, Ideal.mul_sup, Ideal.mul_sup]
    exact sup_le (sup_le Ideal.mul_le_left Ideal.mul_le_left) (sup_le Ideal.mul_le_right hD)
  · calc D = D * (I ⊔ J) := by rw [hIJ, Ideal.mul_top]
      _ = D * I ⊔ D * J := Ideal.mul_sup _ _ _
      _ ≤ (D ⊔ I) * (D ⊔ J) := sup_le (by
          rw [mul_comm]
          exact Ideal.mul_mono le_sup_right le_sup_left)
          (Ideal.mul_mono le_sup_left le_sup_right)

theorem divisorSum_mul {ψ : Ideal (𝓞 K) → ℝ} (hψ : ∀ A B, ψ (A * B) = ψ A * ψ B)
    {I J : Ideal (𝓞 K)} (hIJ : I ⊔ J = ⊤) : divisorSum ψ (I * J) = divisorSum ψ I * divisorSum ψ J := by
  by_cases hI : I = ⊥
  · simp [hI]
  by_cases hJ : J = ⊥
  · simp [hJ]
  have hIJ0 : I * J ≠ ⊥ := mul_ne_zero hI hJ
  rw [divisorSum, divisorSum, divisorSum, Finset.sum_mul_sum, ← Finset.sum_product']
  symm
  refine Finset.sum_bij' (fun p _ ↦ p.1 * p.2) (fun D _ ↦ (D ⊔ I, D ⊔ J)) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    rw [Finset.mem_product, mem_idealDivisors hI, mem_idealDivisors hJ] at hp
    rw [mem_idealDivisors hIJ0]
    exact Ideal.mul_mono hp.1 hp.2
  · intro D hD
    rw [mem_idealDivisors hIJ0] at hD
    rw [Finset.mem_product, mem_idealDivisors hI, mem_idealDivisors hJ]
    exact ⟨le_sup_right, le_sup_right⟩
  · intro p hp
    rw [Finset.mem_product, mem_idealDivisors hI, mem_idealDivisors hJ] at hp
    have h2 : p.1 * p.2 ⊔ J = p.2 := by
      rw [mul_comm]
      exact mul_sup_eq_of_le (by rwa [sup_comm]) hp.2 hp.1
    exact Prod.ext (mul_sup_eq_of_le hIJ hp.1 hp.2) h2
  · intro D hD
    rw [mem_idealDivisors hIJ0] at hD
    exact sup_mul_sup_eq_of_le hIJ hD
  · intro p _
    exact (hψ p.1 p.2).symm

theorem divisorSum_prime_pow {ψ : Ideal (𝓞 K) → ℝ} (hψ : ∀ A B, ψ (A * B) = ψ A * ψ B)
    (hψ1 : ψ ⊤ = 1) {P : Ideal (𝓞 K)} (hP : Prime P) (k : ℕ) :
    divisorSum ψ (P ^ k) = ∑ j ∈ Finset.range (k + 1), ψ P ^ j := by
  have hP0 : P ≠ ⊥ := hP.ne_zero
  have hPk : P ^ k ≠ ⊥ := pow_ne_zero k hP0
  have hψpow : ∀ j : ℕ, ψ (P ^ j) = ψ P ^ j := fun j ↦ by
    induction j with
    | zero => rw [pow_zero, pow_zero, Ideal.one_eq_top, hψ1]
    | succ j ih => rw [pow_succ, pow_succ, hψ, ih]
  have hinj : Function.Injective fun j : ℕ ↦ P ^ j :=
    pow_injective_of_not_isUnit hP.not_isUnit hP0
  have hset : idealDivisors (P ^ k) = (Finset.range (k + 1)).image fun j ↦ P ^ j := by
    ext D
    rw [mem_idealDivisors hPk, Finset.mem_image, ← Ideal.dvd_iff_le, dvd_prime_pow hP]
    simp only [associated_iff_eq, Finset.mem_range, Nat.lt_succ_iff]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i, hi, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i, hi, rfl⟩
  rw [divisorSum, hset, Finset.sum_image fun i _ j _ h ↦ hinj h]
  exact Finset.sum_congr rfl fun j _ ↦ hψpow j

theorem geom_sum_nonneg_of_abs_le_one {x : ℝ} (hx : |x| ≤ 1) (n : ℕ) :
    0 ≤ ∑ j ∈ Finset.range n, x ^ j := by
  rcases eq_or_ne x 1 with rfl | h1
  · simp
  have hlt : x < 1 := lt_of_le_of_ne (le_of_abs_le hx) h1
  rw [geom_sum_eq h1]
  refine div_nonneg_of_nonpos ?_ (by linarith)
  have : x ^ n ≤ 1 := (le_abs_self _).trans (by rw [abs_pow]; exact pow_le_one₀ (abs_nonneg x) hx)
  linarith

theorem divisorSum_nonneg {ψ : Ideal (𝓞 K) → ℝ} (hψ : ∀ A B, ψ (A * B) = ψ A * ψ B)
    (hψ1 : ψ ⊤ = 1) (hψb : ∀ A, |ψ A| ≤ 1) (I : Ideal (𝓞 K)) : 0 ≤ divisorSum ψ I := by
  induction I using UniqueFactorizationMonoid.induction_on_coprime with
  | h0 => rw [Ideal.zero_eq_bot, divisorSum_bot]
  | h1 hu =>
    rw [Ideal.isUnit_iff.1 hu, divisorSum_top, hψ1]
    exact zero_le_one
  | hpr i hp =>
    rw [divisorSum_prime_pow hψ hψ1 hp]
    exact geom_sum_nonneg_of_abs_le_one (hψb _) _
  | hcp hxy hx hy =>
    rename_i x y
    have hsup : x ⊔ y = ⊤ := by
      refine Ideal.isUnit_iff.1 (hxy ?_ ?_)
      · exact Ideal.dvd_iff_le.2 le_sup_left
      · exact Ideal.dvd_iff_le.2 le_sup_right
    rw [divisorSum_mul hψ hsup]
    exact mul_nonneg hx hy

theorem neg_ne_zero_of_one_lt_re {s : ℂ} (hs : 1 < s.re) : -s ≠ 0 :=
  neg_ne_zero.2 fun h ↦ by
    rw [h, zero_re] at hs
    linarith

theorem summable_norm_mul_cpow {ψ : Ideal (𝓞 K) → ℝ} (hψb : ∀ A, |ψ A| ≤ 1) {s : ℂ}
    (hs : 1 < s.re) : Summable fun J : Ideal (𝓞 K) ↦ ‖(ψ J : ℂ) * (absNorm J : ℂ) ^ (-s)‖ := by
  refine ((1 : HeckeCharacter K).summable_norm_coeff_mul_cpow hs).of_nonneg_of_le
    (fun _ ↦ norm_nonneg _) fun J ↦ ?_
  by_cases hJ : J = ⊥
  · simp [hJ, zero_cpow (neg_ne_zero_of_one_lt_re hs)]
  · rw [HeckeCharacter.coeff_one hJ, one_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) (hψb J)

theorem hasSum_divisorSum {ψ : Ideal (𝓞 K) → ℝ} (hψb : ∀ A, |ψ A| ≤ 1) {s : ℂ}
    (hs : 1 < s.re) :
    HasSum (fun I : Ideal (𝓞 K) ↦ (divisorSum ψ I : ℂ) * (absNorm I : ℂ) ^ (-s))
      ((∑' J, (ψ J : ℂ) * (absNorm J : ℂ) ^ (-s)) * dedekindZeta K s) := by
  have hs0 := neg_ne_zero_of_one_lt_re hs
  set f : Ideal (𝓞 K) → ℂ := fun J ↦ (ψ J : ℂ) * (absNorm J : ℂ) ^ (-s) with hf_def
  set g : Ideal (𝓞 K) → ℂ := fun J ↦ (1 : HeckeCharacter K).coeff J * (absNorm J : ℂ) ^ (-s)
    with hg_def
  have hf := summable_norm_mul_cpow hψb hs
  have hg := (1 : HeckeCharacter K).summable_norm_coeff_mul_cpow hs
  have hζ : dedekindZeta K s = ∑' J, g J := by
    rw [← HeckeCharacter.LFunction_one]
    exact ((1 : HeckeCharacter K).hasSum_LFunction hs).tsum_eq.symm
  rw [hζ, tsum_mul_tsum_of_summable_norm hf hg]
  set F : Ideal (𝓞 K) × Ideal (𝓞 K) → ℂ := fun p ↦ f p.1 * g p.2 with hF_def
  have hF : Summable F := summable_mul_of_summable_norm hf hg
  let e := Equiv.sigmaFiberEquiv (fun p : Ideal (𝓞 K) × Ideal (𝓞 K) ↦ p.1 * p.2)
  have h1 : HasSum (F ∘ e) (∑' p, F p) := e.hasSum_iff.2 hF.hasSum
  have h2 := h1.sigma fun I ↦ ((e.summable_iff.2 hF).sigma_factor I).hasSum
  convert h2 using 1
  funext I
  by_cases hI : I = ⊥
  · subst hI
    rw [divisorSum_bot, ofReal_zero, zero_mul]
    symm
    refine (tsum_congr fun q ↦ ?_).trans tsum_zero
    have hq : q.1.1 * q.1.2 = ⊥ := q.2
    change f q.1.1 * g q.1.2 = 0
    rcases Ideal.mul_eq_bot.1 hq with h | h
    · simp [hf_def, h, zero_cpow hs0]
    · simp [hg_def, h]

  have hdvd : ∀ J : {J // J ∈ idealDivisors I}, J.1 ∣ I := fun J ↦
    Ideal.dvd_iff_le.2 ((mem_idealDivisors hI).1 J.2)
  have hfib : ∀ q : {p : Ideal (𝓞 K) × Ideal (𝓞 K) // p.1 * p.2 = I},
      q.1.1 ∈ idealDivisors I := fun q ↦ by
    rw [mem_idealDivisors hI]
    calc I = q.1.1 * q.1.2 := q.2.symm
      _ ≤ q.1.1 := Ideal.mul_le_left
  have hne : ∀ q : {p : Ideal (𝓞 K) × Ideal (𝓞 K) // p.1 * p.2 = I},
      q.1.1 ≠ ⊥ ∧ q.1.2 ≠ ⊥ := fun q ↦ by
    have h := q.2
    constructor <;> intro h0 <;> apply hI <;> rw [← h, h0] <;> simp
  let eqv : {p : Ideal (𝓞 K) × Ideal (𝓞 K) // p.1 * p.2 = I} ≃ {J // J ∈ idealDivisors I} :=
    { toFun := fun q ↦ ⟨q.1.1, hfib q⟩
      invFun := fun J ↦ ⟨(J.1, (hdvd J).choose), (hdvd J).choose_spec.symm⟩
      left_inv := fun q ↦ by
        refine Subtype.ext (Prod.ext rfl ?_)
        have h1 : I = q.1.1 * (hdvd ⟨q.1.1, hfib q⟩).choose := (hdvd ⟨q.1.1, hfib q⟩).choose_spec
        exact mul_left_cancel₀ (hne q).1 (h1.symm.trans q.2.symm)
      right_inv := fun J ↦ rfl }
  have hterm : ∀ q : {p : Ideal (𝓞 K) × Ideal (𝓞 K) // p.1 * p.2 = I},
      (F ∘ e) ⟨I, q⟩ = (ψ (eqv q).1 : ℂ) * (absNorm I : ℂ) ^ (-s) := fun q ↦ by
    change f q.1.1 * g q.1.2 = (ψ q.1.1 : ℂ) * (absNorm I : ℂ) ^ (-s)
    rw [hf_def, hg_def]
    simp only
    rw [HeckeCharacter.coeff_one (hne q).2, one_mul, mul_assoc, ← natCast_mul_natCast_cpow,
      ← Nat.cast_mul, ← map_mul, q.2]
  rw [tsum_congr hterm, tsum_mul_right, Equiv.tsum_eq eqv (fun J ↦ (ψ J.1 : ℂ)),
    Finset.tsum_subtype (idealDivisors I) (fun J ↦ (ψ J : ℂ)), divisorSum, ofReal_sum]

def divisorSumCoeff (ψ : Ideal (𝓞 K) → ℝ) (n : ℕ) : ℂ :=
  ∑' I : {I : Ideal (𝓞 K) // absNorm I = n}, (divisorSum ψ I : ℂ)

theorem hasSum_LSeries_term_divisorSum {ψ : Ideal (𝓞 K) → ℝ} (hψb : ∀ A, |ψ A| ≤ 1) {s : ℂ}
    (hs : 1 < s.re) :
    HasSum (LSeries.term (divisorSumCoeff ψ) s)
      ((∑' J, (ψ J : ℂ) * (absNorm J : ℂ) ^ (-s)) * dedekindZeta K s) := by
  have hs0 := neg_ne_zero_of_one_lt_re hs
  have hsum := hasSum_divisorSum hψb hs
  set h : Ideal (𝓞 K) → ℂ := fun I ↦ (divisorSum ψ I : ℂ) * (absNorm I : ℂ) ^ (-s) with hh
  let e := Equiv.sigmaFiberEquiv (fun I : Ideal (𝓞 K) ↦ absNorm I)
  have h1 : HasSum (h ∘ e) _ := e.hasSum_iff.2 hsum
  have h2 := h1.sigma fun n ↦ ((e.summable_iff.2 hsum.summable).sigma_factor n).hasSum
  convert h2 using 1
  funext n
  rw [LSeries.term_def]
  split_ifs with hn
  · subst hn
    symm
    refine (tsum_congr fun y ↦ ?_).trans tsum_zero
    have hy : (y : Ideal (𝓞 K)) = ⊥ := absNorm_eq_zero_iff.1 y.2
    simp [e, hh, hy]
  · rw [divisorSumCoeff, ← tsum_div_const]
    refine tsum_congr fun y ↦ ?_
    simp [e, hh, y.2, cpow_neg, div_eq_mul_inv]

open scoped ComplexOrder in

theorem divisorSumCoeff_nonneg {ψ : Ideal (𝓞 K) → ℝ} (hψ : ∀ A B, ψ (A * B) = ψ A * ψ B)
    (hψ1 : ψ ⊤ = 1) (hψb : ∀ A, |ψ A| ≤ 1) (n : ℕ) : 0 ≤ divisorSumCoeff ψ n := by
  rw [divisorSumCoeff, ← Complex.ofReal_tsum]
  exact Complex.zero_le_real.2 (tsum_nonneg fun I ↦ divisorSum_nonneg hψ hψ1 hψb I)

theorem divisorSumCoeff_one (ψ : Ideal (𝓞 K) → ℝ) : divisorSumCoeff ψ 1 = ψ ⊤ := by
  rw [divisorSumCoeff, tsum_eq_single ⟨⊤, absNorm_top⟩]
  · rw [divisorSum_top]
  · intro I hI
    exact absurd (Subtype.ext (absNorm_eq_one_iff.1 I.2)) hI

end

end GroundTheory.Global
