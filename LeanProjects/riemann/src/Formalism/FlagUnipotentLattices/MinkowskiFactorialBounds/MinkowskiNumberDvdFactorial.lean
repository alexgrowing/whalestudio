import Formalism.FlagUnipotentLattices.MemOfOrthogonalAnisotropic
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.ExistsHasLeadingCoeffOfMemSpanBelow
import Formalism.HyperbolicPlaceProducts.SecondLevelArithmeticNorm

open Formalism.HermitianLatticeCounting.S6
open scoped BigOperators
open Matrix

namespace Formalism.HermitianLatticeCounting.P

theorem norm_singular_value_bound : Formalism.HermitianLatticeCounting.S6.NormSgBound := by
  intro ι _ r f D sg H₁ Hh hf hH hHh hD0 hsg hD
  have hp0 : (0:ℝ) < (2 * H₁) ^ (2 * r) := by
    have : (0:ℝ) < 2 * H₁ := by linarith
    positivity
  have h1 : ∀ v, D v ≤ (2 * H₁) ^ (2 * r) * sg v := fun v => by
    have := hD v
    rw [div_le_iff₀ hp0] at this; rw [mul_comm]; exact this
  calc ∏ v, D v ^ 2 ≤ ∏ v, ((2 * H₁) ^ (2 * r) * sg v) ^ 2 :=
        Finset.prod_le_prod (fun v _ => by positivity) (fun v _ => pow_le_pow_left₀ (hD0 v) (h1 v) 2)
    _ = (2 * H₁) ^ (4 * r * f) * ∏ v, sg v ^ 2 := by
        simp_rw [mul_pow]
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, hf, ← pow_mul, ← pow_mul]
        congr 2; ring
    _ ≤ Hh * ∏ v, sg v ^ 2 := by
        apply mul_le_mul_of_nonneg_right hHh
        exact Finset.prod_nonneg (fun v _ => by positivity)

theorem coefficient_field_bound : Formalism.HermitianLatticeCounting.S6.CfBound := by
  intro f x k hf hx
  have hx1 : (1:ℝ) ≤ x := by exact_mod_cast hx
  have hx0 : (0:ℝ) < x := by linarith
  have h1 := Formalism.SLP.Final.omegaPow (2 * f) x (by omega) hx
  have e : (((2 * f : ℕ) : ℝ)) = 2 * (f : ℝ) := by push_cast; ring
  rw [e] at h1 ⊢
  calc (2 * (f:ℝ)) ^ (Nat.primeFactorsList x).length * (x : ℝ) ^ k
      ≤ (x : ℝ) ^ Real.logb 2 (2 * f) * (x : ℝ) ^ k :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = (x : ℝ) ^ ((k : ℝ) + Real.logb 2 (2 * f)) := by
        rw [Real.rpow_add hx0, Real.rpow_natCast, mul_comm]
    _ ≤ (x : ℝ) ^ ((k : ℝ) + (1 + Real.logb 2 (2 * f))) :=
        Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)

lemma sublatticeCount_of (hS : Formalism.SLP.SubmoduleIndexCountO) (hC : Formalism.HermitianLatticeCounting.S6.CfBound) :
    Formalism.HermitianLatticeCounting.S6.SublatticeCount := by
  intro E _ _ M _ _ _ _ f x hE hx
  obtain ⟨h1, h2⟩ := hS E M x hx
  refine ⟨h1, ?_⟩
  have hf : 1 ≤ f := by
    have : 0 < Module.finrank ℚ E := Module.finrank_pos
    omega
  rw [hE] at h2
  have h3 : (({N : Submodule (NumberField.RingOfIntegers E) M | N.toAddSubgroup.index = x}.ncard : ℕ) : ℝ) ≤
      ((2 * f : ℕ) : ℝ) ^ (Nat.primeFactorsList x).length *
        (x : ℝ) ^ Module.finrank (NumberField.RingOfIntegers E) M := by exact_mod_cast h2
  exact le_trans h3 (hC f x _ hf hx)

theorem sublattice_count_alt : Formalism.HermitianLatticeCounting.S6.SublatticeCount :=
  sublatticeCount_of Formalism.SLP.Final.submoduleIndexCountO coefficient_field_bound

theorem exponential_identity : Formalism.HermitianLatticeCounting.S6.ExpIdentity := by
  intro k j D hD
  rw [← Real.rpow_add hD]
  congr 1
  ring

lemma norm_det_le (n : ℕ) (M : Matrix (Fin n) (Fin n) ℂ) (β : ℝ) (hM : ∀ i j, ‖M i j‖ ≤ β) :
    ‖M.det‖ ≤ (n.factorial : ℝ) * β ^ n := by
  rw [Matrix.det_apply]
  calc ‖∑ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ • ∏ i, M (σ i) i‖
      ≤ ∑ σ : Equiv.Perm (Fin n), ‖Equiv.Perm.sign σ • ∏ i, M (σ i) i‖ := norm_sum_le _ _
    _ ≤ ∑ _σ : Equiv.Perm (Fin n), β ^ n := by
        apply Finset.sum_le_sum
        intro σ _
        have h1 : ‖Equiv.Perm.sign σ • ∏ i, M (σ i) i‖ = ‖∏ i, M (σ i) i‖ := by
          rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
        rw [h1, norm_prod]
        calc ∏ i, ‖M (σ i) i‖ ≤ ∏ _i : Fin n, β :=
              Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ => hM _ _)
          _ = β ^ n := by simp
    _ = (n.factorial : ℝ) * β ^ n := by
        simp [Fintype.card_perm]

lemma prod_primepow_dvd (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (e : ℕ → ℕ) (n : ℕ)
    (h : ∀ p ∈ s, p ^ e p ∣ n) : ∏ p ∈ s, p ^ e p ∣ n := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert p s hp ih =>
    rw [Finset.prod_insert hp]
    apply Nat.Coprime.mul_dvd_of_dvd_of_dvd _ (h p (Finset.mem_insert_self _ _))
      (ih (fun q hq => hs q (Finset.mem_insert_of_mem hq)) (fun q hq => h q (Finset.mem_insert_of_mem hq)))
    apply Nat.Coprime.prod_right
    intro q hq
    apply Nat.Coprime.pow
    exact (Nat.coprime_primes (hs p (Finset.mem_insert_self _ _)) (hs q (Finset.mem_insert_of_mem hq))).2
      (fun hpq => hp (hpq ▸ hq))

theorem minkowski_number_dvd_factorial : Formalism.HermitianLatticeCounting.S6.MinkowskiDvdFactorial := by
  intro N
  unfold minkowskiM
  apply prod_primepow_dvd _ (fun p hp => (Finset.mem_filter.1 hp).2)
  intro p hp
  have hpp : p.Prime := (Finset.mem_filter.1 hp).2
  have := Fact.mk hpp
  have hp2 : 2 ≤ p := hpp.two_le
  rw [padicValNat_dvd_iff_le (Nat.factorial_ne_zero _)]
  have hlog : Nat.log p (2 * N) < N + 2 := by
    by_cases h0 : 2 * N = 0
    · simp [h0]
    · apply Nat.log_lt_of_lt_pow h0
      have h1 : N < 2 ^ N := Nat.lt_two_pow_self
      have h2 : 2 ^ (N + 2) = 4 * 2 ^ N := by ring
      have h3 : 2 ^ (N + 2) ≤ p ^ (N + 2) := Nat.pow_le_pow_left hp2 _
      omega
  rw [padicValNat_factorial hlog, Finset.sum_Ico_eq_sum_range]
  unfold minkowskiExp
  have e : N + 2 - 1 = N + 1 := by omega
  rw [e]
  apply Finset.sum_le_sum
  intro i _
  have hpos : 0 < p ^ (1 + i) := pow_pos (by omega) _
  have hle : p ^ (1 + i) ≤ 2 * (p ^ i * (p - 1)) := by
    have h1 : p ≤ 2 * (p - 1) := by omega
    calc p ^ (1 + i) = p ^ i * p := by ring
      _ ≤ p ^ i * (2 * (p - 1)) := Nat.mul_le_mul_left _ h1
      _ = 2 * (p ^ i * (p - 1)) := by ring
  calc N / (p ^ i * (p - 1)) = (2 * N) / (2 * (p ^ i * (p - 1))) := by
        rw [Nat.mul_div_mul_left _ _ (by norm_num : 0 < 2)]
    _ ≤ (2 * N) / p ^ (1 + i) := Nat.div_le_div_left hle hpos

theorem automorphism_bound_of_hyp : Formalism.HermitianLatticeCounting.S6.AutBoundAsm := by
  intro hM hD s f G hG
  have h1 := (hM (2 * s * f) G hG).trans (hD (2 * s * f))
  have h2 := Nat.le_of_dvd (Nat.factorial_pos _) h1
  have h3 := h2.trans (Nat.factorial_le_pow _)
  have e : 2 * (2 * s * f) = 4 * s * f := by ring
  rw [e] at h3
  exact_mod_cast h3

theorem exterior_power_bound : Formalism.HermitianLatticeCounting.S6.ExtPowerBound := by
  intro j m A A' Z hyp
  let B : EuclideanSpace ℂ (Fin m) →ₗ[ℂ] EuclideanSpace ℂ (Fin m) →ₗ⋆[ℂ] ℂ :=
    LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ)
      (fun x y => ∑ a, ∑ b, (A *ᵥ x.ofLp) a * Z a b * star ((A' *ᵥ y.ofLp) b))
      (by
        intro x x' y
        simp only [WithLp.ofLp_add, Matrix.mulVec_add, Pi.add_apply, add_mul, Finset.sum_add_distrib])
      (by
        intro c x y
        simp only [WithLp.ofLp_smul, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
          Finset.mul_sum, mul_assoc])
      (by
        intro x y y'
        simp only [WithLp.ofLp_add, Matrix.mulVec_add, Pi.add_apply, star_add, mul_add,
          Finset.sum_add_distrib])
      (by
        intro c x y
        simp only [WithLp.ofLp_smul, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, star_mul',
          Finset.mul_sum, starRingEnd_apply]
        apply Finset.sum_congr rfl; intro a _
        apply Finset.sum_congr rfl; intro b _
        ring)
  have hBdef : ∀ x y, B x y = ∑ a, ∑ b, (A *ᵥ x.ofLp) a * Z a b * star ((A' *ᵥ y.ofLp) b) :=
    fun _ _ => rfl
  have hB1 : ∀ x y : EuclideanSpace ℂ (Fin m), ‖x‖ = 1 → ‖y‖ = 1 → ‖B x y‖ ≤ 2 := by
    intro x y hx hy
    rw [hBdef]
    apply hyp
    · have := EuclideanSpace.norm_sq_eq x
      rw [hx] at this
      simpa using this.symm.le
    · have := EuclideanSpace.norm_sq_eq y
      rw [hy] at this
      simpa using this.symm.le
  have hB : ∀ x y, ‖B x y‖ ≤ 2 * ‖x‖ * ‖y‖ := by
    intro x y
    by_cases hx : x = 0
    · simp [hx]
    by_cases hy : y = 0
    · simp [hy]
    have hx0 : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
    have hy0 : ‖y‖ ≠ 0 := norm_ne_zero_iff.2 hy
    have h1 := hB1 (((‖x‖ : ℂ))⁻¹ • x) (((‖y‖ : ℂ))⁻¹ • y)
      (by rw [norm_smul, norm_inv, Complex.norm_real, norm_norm, inv_mul_cancel₀ hx0])
      (by rw [norm_smul, norm_inv, Complex.norm_real, norm_norm, inv_mul_cancel₀ hy0])
    have e0 : B (((‖x‖ : ℂ))⁻¹ • x) (((‖y‖ : ℂ))⁻¹ • y) = (((‖x‖ : ℂ))⁻¹ * ((‖y‖ : ℂ))⁻¹) * B x y := by
      simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, map_inv₀, Complex.conj_ofReal,
        RingHom.id_apply]
      ring
    rw [e0, norm_mul, norm_mul, norm_inv, norm_inv, Complex.norm_real, Complex.norm_real, norm_norm,
      norm_norm] at h1
    have hxp : 0 < ‖x‖ := norm_pos_iff.2 hx
    have hyp' : 0 < ‖y‖ := norm_pos_iff.2 hy
    have e : ‖x‖⁻¹ * ‖y‖⁻¹ * ‖B x y‖ = ‖B x y‖ / (‖x‖ * ‖y‖) := by field_simp
    rw [e, div_le_iff₀ (by positivity)] at h1
    linarith
  let u : Fin j → EuclideanSpace ℂ (Fin m) := fun i => WithLp.toLp 2 (fun l => star (A i l))
  let w : Fin j → EuclideanSpace ℂ (Fin m) := fun i => WithLp.toLp 2 (fun l => star (A' i l))
  have hgram : ∀ (M : Matrix (Fin j) (Fin m) ℂ),
      Matrix.gram ℂ (fun i => (WithLp.toLp 2 (fun l => star (M i l)) : EuclideanSpace ℂ (Fin m))) = M * Mᴴ := by
    intro M
    ext i k
    rw [Matrix.gram_apply, PiLp.inner_apply, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro l _
    simp [Matrix.conjTranspose_apply, mul_comm]
  have hmv : ∀ (M : Matrix (Fin j) (Fin m) ℂ) (i a : Fin j),
      (M *ᵥ (fun l => star (M i l))) a = (M * Mᴴ) a i := by
    intro M i a
    simp [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.conjTranspose_apply]
  have hmat : (Matrix.of fun i k => B (u i) (w k)) = (A * Aᴴ)ᵀ * Z * ((A' * A'ᴴ)ᴴ)ᵀ := by
    ext i k
    simp only [Matrix.of_apply, hBdef, u, w, hmv]
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_apply (M := (A * Aᴴ)ᵀ), Matrix.transpose_apply, Matrix.conjTranspose_apply,
      Finset.sum_mul]
    rw [Finset.sum_comm]
  have h := Formalism.SLP.Final.sesqDet _ _ B 2 hB j u w
  rw [hmat, hgram A, hgram A', Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_transpose,
    Matrix.det_conjTranspose, norm_mul, norm_mul, norm_star] at h
  set p := ‖(A * Aᴴ).det‖ with hp
  set q := ‖(A' * A'ᴴ).det‖ with hq
  set z := ‖Z.det‖ with hz
  have hp0 : 0 ≤ p := norm_nonneg _
  have hq0 : 0 ≤ q := norm_nonneg _
  apply le_of_pow_le_pow_left₀ two_ne_zero (by positivity)
  rw [mul_pow, mul_pow, Real.sq_sqrt hp0, Real.sq_sqrt hq0, ← pow_mul, mul_comm j 2]
  by_cases hpq : p * q = 0
  · rw [hpq, zero_mul]; positivity
  · have hpos : 0 < p * q := lt_of_le_of_ne (mul_nonneg hp0 hq0) (Ne.symm hpq)
    apply le_of_mul_le_mul_left _ hpos
    calc p * q * (p * q * z ^ 2) = (p * z * q) ^ 2 := by ring
      _ ≤ 2 ^ (2 * j) * p * q := h
      _ = p * q * 2 ^ (2 * j) := by ring

lemma fs_sizes (C m M6 Q L kR lam : ℝ) (hC : 1 ≤ C) (hM64 : 64 ≤ M6) (hmM : m * m ≤ M6)
    (hQ : 0 ≤ Q) (hL2 : 1 / 2 ≤ L) (hk0 : 0 ≤ kR) (hlk : lam ≤ kR)
    (hyp : (16 * C + Q * Q) * M6 * L ≤ kR * lam) :
    8 ≤ kR ∧ m ≤ kR ∧ Q ≤ kR ∧ M6 ≤ 2 * (M6 * L) ∧ 16 * (M6 * L) ≤ kR * lam ∧
      16 * C * (M6 * L) ≤ kR * lam := by
  have hM0 : 0 ≤ M6 := by linarith
  have hmE : M6 ≤ 2 * (M6 * L) := by
    have := mul_le_mul_of_nonneg_left hL2 hM0
    linarith
  have hE32 : 32 ≤ M6 * L := by linarith
  have hE0 : 0 ≤ M6 * L := by linarith
  have hQQ : 0 ≤ Q * Q * (M6 * L) := mul_nonneg (mul_nonneg hQ hQ) hE0
  have hCE0 : M6 * L ≤ C * (M6 * L) := le_mul_of_one_le_left hE0 hC
  have e : (16 * C + Q * Q) * M6 * L = 16 * (C * (M6 * L)) + Q * Q * (M6 * L) := by ring
  rw [e] at hyp
  have hkk : kR * lam ≤ kR * kR := mul_le_mul_of_nonneg_left hlk hk0
  have hQ32 : Q * Q ≤ Q * Q * (M6 * L) := le_mul_of_one_le_right (mul_nonneg hQ hQ) (by linarith)
  refine ⟨?_, ?_, ?_, hmE, by linarith, by linarith⟩
  · by_contra h
    have h' : kR < 8 := not_le.1 h
    have := mul_self_lt_mul_self hk0 h'
    linarith
  · by_contra h
    have h' : kR < m := not_le.1 h
    have := mul_self_lt_mul_self hk0 h'
    linarith
  · by_contra h
    have h' : kR < Q := not_le.1 h
    have := mul_self_lt_mul_self hk0 h'
    linarith

lemma fs_arith (C M6 L kR fR lam lC : ℝ) (hf1 : 1 ≤ fR) (hk8 : 8 ≤ kR) (hl0 : 0 ≤ lam)
    (hmE : M6 ≤ 2 * (M6 * L)) (hE16 : 16 * (M6 * L) ≤ kR * lam) (hCE : 16 * C * (M6 * L) ≤ kR * lam)
    (hlogC : 16 * lC ≤ lam) :
    M6 + (C * M6 * fR * L + C * M6 * fR * L) +
      ((kR - 2) * fR * (lC - lam) + (kR - 2) * fR * (lC - lam)) ≤ -(kR * fR * lam) := by
  have hf0 : 0 ≤ fR := by linarith
  have hk0 : 0 ≤ kR := by linarith
  have hfl : 0 ≤ fR * lam := mul_nonneg hf0 hl0
  have b0 : kR * lam ≤ kR * fR * lam := by
    have h1 := mul_nonneg (mul_nonneg hk0 hl0) (sub_nonneg.2 hf1)
    have e : kR * fR * lam - kR * lam = kR * lam * (fR - 1) := by ring
    linarith
  have b2 : 2 * (C * M6 * fR * L) ≤ kR * fR * lam / 8 := by
    have h := mul_le_mul_of_nonneg_left hCE hf0
    have e1 : 2 * (C * M6 * fR * L) = fR * (16 * C * (M6 * L)) / 8 := by ring
    have e2 : fR * (kR * lam) = kR * fR * lam := by ring
    linarith
  have b3 : 2 * ((kR - 2) * fR * lC) ≤ kR * fR * lam / 8 := by
    have h1 : (kR - 2) * fR * (16 * lC) ≤ (kR - 2) * fR * lam :=
      mul_le_mul_of_nonneg_left hlogC (mul_nonneg (by linarith) hf0)
    have e1 : 2 * ((kR - 2) * fR * lC) = (kR - 2) * fR * (16 * lC) / 8 := by ring
    have e2 : (kR - 2) * fR * lam = kR * fR * lam - 2 * (fR * lam) := by ring
    linarith
  have b4 : 8 * (fR * lam) ≤ kR * fR * lam := by
    have h := mul_le_mul_of_nonneg_right hk8 hfl
    have e : kR * (fR * lam) = kR * fR * lam := by ring
    linarith
  have e : M6 + (C * M6 * fR * L + C * M6 * fR * L) +
      ((kR - 2) * fR * (lC - lam) + (kR - 2) * fR * (lC - lam)) =
      M6 + 2 * (C * M6 * fR * L) + 2 * ((kR - 2) * fR * lC) - 2 * (kR * fR * lam) + 4 * (fR * lam) := by ring
  rw [e]
  linarith

lemma fs_exp (j k f : ℕ) (hj1 : 1 ≤ j) (hjk : j + 2 ≤ k) : (k - 2) * f ≤ j * (k - 1 - j) * f := by
  apply Nat.mul_le_mul_right
  obtain ⟨t, rfl⟩ : ∃ t, k = j + 2 + t := ⟨k - (j + 2), by omega⟩
  have e1 : j + 2 + t - 1 - j = t + 1 := by omega
  have e2 : j + 2 + t - 2 = j + t := by omega
  rw [e1, e2]
  calc j + t ≤ j + j * t := Nat.add_le_add_left (Nat.le_mul_of_pos_left t hj1) j
    _ = j * (t + 1) := by ring

lemma fs_sum (A x : ℝ) (hA0 : 0 ≤ A) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (k r f : ℕ) (hk : r + 2 ≤ k) :
    0 ≤ ∑ j ∈ Finset.Icc 1 r, A * x ^ (j * (k - 1 - j) * f) ∧
    ∑ j ∈ Finset.Icc 1 r, A * x ^ (j * (k - 1 - j) * f) ≤ r * (A * x ^ ((k - 2) * f)) := by
  refine ⟨Finset.sum_nonneg (fun j _ => by positivity), ?_⟩
  have hterm : ∀ j ∈ Finset.Icc 1 r, A * x ^ (j * (k - 1 - j) * f) ≤ A * x ^ ((k - 2) * f) := by
    intro j hj
    obtain ⟨hj1, hjr⟩ := Finset.mem_Icc.1 hj
    apply mul_le_mul_of_nonneg_left _ hA0
    exact pow_le_pow_of_le_one hx0 hx1 (fs_exp j k f hj1 (by omega))
  have := Finset.sum_le_card_nsmul (Finset.Icc 1 r) (fun j => A * x ^ (j * (k - 1 - j) * f)) _ hterm
  rw [Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul] at this
  exact this

theorem final_sum_bound : Formalism.HermitianLatticeCounting.S6.FinalSum := by
  intro C hC
  refine ⟨16 * C + C ^ 32, by positivity, ?_⟩
  intro k r f b d hb hf hd hyp
  have hr0 : (0:ℝ) ≤ r := Nat.cast_nonneg r
  have hmr : ((2 * r + 2 : ℕ) : ℝ) = 2 * r + 2 := by push_cast; ring
  generalize hm : ((2 * r + 2 : ℕ) : ℝ) = m at hyp hmr ⊢
  have hm2 : 2 ≤ m := by rw [hmr]; linarith
  have hL2 : 1 / 2 ≤ Real.log b := by
    have h1 : Real.log 2 ≤ Real.log b := Real.log_le_log (by norm_num) hb
    have h2 := Real.log_two_gt_d9
    linarith
  generalize Real.log b = L at hyp hL2 ⊢
  have hf1 : (1:ℝ) ≤ f := by exact_mod_cast hf
  have hk0 : (0:ℝ) ≤ k := Nat.cast_nonneg k
  have hm6 : (64:ℝ) ≤ m ^ 6 := by
    calc (64:ℝ) = 2 ^ 6 := by norm_num
      _ ≤ m ^ 6 := pow_le_pow_left₀ (by norm_num) hm2 6
  have hm62 : m * m ≤ m ^ 6 := by
    rw [← sq]; exact pow_le_pow_right₀ (by linarith) (by norm_num)
  have e32 : C ^ 32 = C ^ 16 * C ^ 16 := by ring
  rw [e32] at hyp
  obtain ⟨hk8, hkm, hkC, hmE, hE16, hCE⟩ := fs_sizes C m (m ^ 6) (C ^ 16) L k (Real.log k) hC hm6
    hm62 (by positivity) hL2 hk0 (Real.log_le_self hk0) hyp
  have hkpos : (0:ℝ) < k := by linarith
  have hl0 : 0 ≤ Real.log (k:ℝ) := Real.log_nonneg (by linarith)
  have hlogC : 16 * Real.log C ≤ Real.log (k:ℝ) := by
    have := Real.log_le_log (by positivity) hkC
    rw [Real.log_pow] at this
    simpa using this
  have hkN : 2 * r + 2 ≤ k := by
    rw [← hm] at hkm
    exact_mod_cast hkm
  have hx0 : 0 < C / (k:ℝ) := by positivity
  have hx1 : C / (k:ℝ) ≤ 1 := by
    rw [div_le_one hkpos]
    exact le_trans (le_self_pow₀ hC (by norm_num)) hkC
  obtain ⟨hS0, hS1⟩ := fs_sum (Real.exp (C * m ^ 6 * f * L)) (C / (k:ℝ)) (Real.exp_pos _).le hx0.le hx1 k r f
    (by omega)
  generalize (∑ j ∈ Finset.Icc 1 r, Real.exp (C * m ^ 6 * f * L) * (C / (k:ℝ)) ^ (j * (k - 1 - j) * f)) = S
    at hS0 hS1 ⊢
  have hxn : (C / (k:ℝ)) ^ ((k - 2) * f) =
      Real.exp ((((k:ℝ) - 2) * f) * (Real.log C - Real.log (k:ℝ))) := by
    have hncast : (((k - 2) * f : ℕ) : ℝ) = ((k:ℝ) - 2) * f := by
      push_cast [Nat.cast_sub (by omega : 2 ≤ k)]; ring
    rw [← hncast, ← Real.log_div (by positivity) hkpos.ne', Real.exp_nat_mul, Real.exp_log hx0]
  rw [hxn] at hS1
  have h2r : 2 * (r:ℝ) ^ 2 ≤ Real.exp (m ^ 6) := by
    have h1 : 2 * (r:ℝ) ^ 2 ≤ m * m := by rw [hmr]; nlinarith
    have h2 := Real.add_one_le_exp (m ^ 6)
    linarith
  have har := fs_arith C (m ^ 6) L k f (Real.log k) (Real.log C) hf1 hk8 hl0 hmE hE16 hCE hlogC
  have hmain : 2 * S ^ 2 ≤ Real.exp (-((k:ℝ) * f * Real.log k)) := by
    calc 2 * S ^ 2 ≤ 2 * (r * (Real.exp (C * m ^ 6 * f * L) *
            Real.exp ((((k:ℝ) - 2) * f) * (Real.log C - Real.log (k:ℝ))))) ^ 2 := by
          have := pow_le_pow_left₀ hS0 hS1 2
          linarith
      _ = (2 * (r:ℝ) ^ 2) * ((Real.exp (C * m ^ 6 * f * L) * Real.exp (C * m ^ 6 * f * L)) *
            (Real.exp ((((k:ℝ) - 2) * f) * (Real.log C - Real.log (k:ℝ))) *
              Real.exp ((((k:ℝ) - 2) * f) * (Real.log C - Real.log (k:ℝ))))) := by ring
      _ ≤ Real.exp (m ^ 6) * ((Real.exp (C * m ^ 6 * f * L) * Real.exp (C * m ^ 6 * f * L)) *
            (Real.exp ((((k:ℝ) - 2) * f) * (Real.log C - Real.log (k:ℝ))) *
              Real.exp ((((k:ℝ) - 2) * f) * (Real.log C - Real.log (k:ℝ))))) :=
          mul_le_mul_of_nonneg_right h2r (by positivity)
      _ = Real.exp (m ^ 6 + (C * m ^ 6 * f * L + C * m ^ 6 * f * L) +
            ((((k:ℝ) - 2) * f) * (Real.log C - Real.log (k:ℝ)) +
              (((k:ℝ) - 2) * f) * (Real.log C - Real.log (k:ℝ)))) := by
          rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
          congr 1
          ring
      _ ≤ Real.exp (-((k:ℝ) * f * Real.log k)) := Real.exp_le_exp.2 har
  calc 2 * d * S ^ 2 = d * (2 * S ^ 2) := by ring
    _ ≤ d * Real.exp (-((k:ℝ) * f * Real.log k)) := mul_le_mul_of_nonneg_left hmain hd

section DetK

variable {K U : Type} [Field K] [StarRing K] [AddCommGroup U] [Module K U]

lemma gsK (h : U →ₗ[K] U →ₗ⋆[K] K) (herm : ∀ x y : U, star (h x y) = h y x)
    (haniso : ∀ x : U, h x x = 0 → x = 0) :
    ∀ (s : ℕ) (w : Fin s → U), ∃ (g : Fin s → U) (L : Matrix (Fin s) (Fin s) K), L.det = 1 ∧
      (∀ b, w b = ∑ c, L b c • g c) ∧ (∀ a b, a ≠ b → h (g a) (g b) = 0) := by
  intro s
  induction s with
  | zero => intro w; exact ⟨fun a => a.elim0, 1, by simp, fun b => b.elim0, fun a => a.elim0⟩
  | succ s ih =>
    intro w
    obtain ⟨g₀, L₀, hdet, hw₀, horth⟩ := ih (fun b => w b.castSucc)
    let t : Fin s → K := fun c => h (w (Fin.last s)) (g₀ c) / h (g₀ c) (g₀ c)
    let gl : U := w (Fin.last s) - ∑ c, t c • g₀ c
    let g : Fin (s + 1) → U := Fin.lastCases (motive := fun _ => U) gl g₀
    let L : Matrix (Fin (s + 1)) (Fin (s + 1)) K := Matrix.of fun b c =>
      Fin.lastCases (motive := fun _ => K) (Fin.lastCases (motive := fun _ => K) 1 t c)
        (fun b' => Fin.lastCases (motive := fun _ => K) 0 (L₀ b') c) b
    have hgc : ∀ c, g c.castSucc = g₀ c := by intro c; simp [g]
    have hgl : g (Fin.last s) = gl := by simp [g]
    have hLcc : ∀ b c, L b.castSucc c.castSucc = L₀ b c := by intro b c; simp [L]
    have hLcl : ∀ b : Fin s, L b.castSucc (Fin.last s) = 0 := by intro b; simp [L]
    have hLlc : ∀ c : Fin s, L (Fin.last s) c.castSucc = t c := by intro c; simp [L]
    have hLll : L (Fin.last s) (Fin.last s) = 1 := by simp [L]
    have hglo : ∀ b, h gl (g₀ b) = 0 := by
      intro b
      simp only [gl, map_sub, map_sum, map_smul, LinearMap.sub_apply, LinearMap.sum_apply,
        LinearMap.smul_apply, smul_eq_mul]
      rw [Finset.sum_eq_single b]
      · by_cases h0 : h (g₀ b) (g₀ b) = 0
        · have := haniso _ h0
          simp [this]
        · simp only [t]; rw [div_mul_cancel₀ _ h0, sub_self]
      · intro c _ hc; rw [horth c b hc, mul_zero]
      · intro hb; exact absurd (Finset.mem_univ b) hb
    refine ⟨g, L, ?_, ?_, ?_⟩
    · rw [Matrix.det_succ_column L (Fin.last s), Fin.sum_univ_castSucc]
      simp only [hLcl, hLll, mul_zero, zero_mul, Finset.sum_const_zero, zero_add, mul_one]
      have e : (L.submatrix (Fin.last s).succAbove (Fin.last s).succAbove) = L₀ := by
        ext a b; simp [Fin.succAbove_last, hLcc]
      have e2 : ((-1 : K)) ^ ((Fin.last s : Fin (s+1)).val + (Fin.last s : Fin (s+1)).val) = 1 := by
        rw [← two_mul, pow_mul]; simp
      rw [e, hdet, e2, one_mul]
    · intro b
      refine Fin.lastCases ?_ (fun b' => ?_) b
      · rw [Fin.sum_univ_castSucc]
        simp only [hLlc, hLll, hgc, hgl, one_smul]
        simp [gl]
      · rw [Fin.sum_univ_castSucc]
        simp only [hLcc, hLcl, hgc, zero_smul, add_zero]
        exact hw₀ b'
    · intro a b hab
      rcases Fin.eq_castSucc_or_eq_last a with ⟨a', rfl⟩ | rfl <;>
        rcases Fin.eq_castSucc_or_eq_last b with ⟨b', rfl⟩ | rfl
      · rw [hgc, hgc]; exact horth a' b' (fun e => hab (by rw [e]))
      · rw [hgc, hgl, ← herm, hglo, star_zero]
      · rw [hgl, hgc]; exact hglo b'
      · exact absurd rfl hab

lemma bmatK (h' : U →ₗ[K] U →ₗ⋆[K] K) {m : ℕ} (e f : Fin m → U) (A C : Matrix (Fin m) (Fin m) K)
    (u w : Fin m → U) (hu : ∀ i, u i = ∑ k, A i k • e k) (hw : ∀ j, w j = ∑ l, C j l • f l) :
    (Matrix.of fun i j => h' (u i) (w j)) = A * (Matrix.of fun k l => h' (e k) (f l)) * Cᴴ := by
  ext i j
  simp only [Matrix.of_apply, hu, hw, map_sum, map_smul, LinearMap.sum_apply,
    LinearMap.smul_apply, map_smulₛₗ, smul_eq_mul, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Finset.sum_mul, Finset.mul_sum, starRingEnd_apply]
  exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by ring

lemma herm_real (σ : K →+* ℂ) (h : U →ₗ[K] U →ₗ⋆[K] K) (hσ : ∀ x : K, σ (star x) = star (σ x))
    (herm : ∀ x y : U, star (h x y) = h y x) (x : U) : σ (h x x) = (((σ (h x x)).re : ℝ) : ℂ) := by
  apply Complex.ext
  · simp
  · simp [herm_im σ h hσ herm x]

lemma besselK (σ : K →+* ℂ) (h : U →ₗ[K] U →ₗ⋆[K] K) (hσ : ∀ x : K, σ (star x) = star (σ x))
    (herm : ∀ x y : U, star (h x y) = h y x) (hnn : ∀ x : U, 0 ≤ (σ (h x x)).re) {s : ℕ}
    (g : Fin s → U) (horth : ∀ a b, a ≠ b → h (g a) (g b) = 0) (hd : ∀ a, h (g a) (g a) ≠ 0) (y : U) :
    ∑ a, ‖σ (h (g a) y)‖ ^ 2 / (σ (h (g a) (g a))).re ≤ (σ (h y y)).re := by
  let c : Fin s → K := fun a => h y (g a) / h (g a) (g a)
  set y' : U := y - ∑ a, c a • g a with hy'
  have h1 : ∀ b, h y' (g b) = 0 := by
    intro b
    simp only [hy', map_sub, map_sum, map_smul, LinearMap.sub_apply, LinearMap.sum_apply,
      LinearMap.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single b]
    · simp only [c]; rw [div_mul_cancel₀ _ (hd b), sub_self]
    · intro a _ ha; rw [horth a b ha, mul_zero]
    · intro hb; exact absurd (Finset.mem_univ b) hb
  have h2 : h y' y' = h y' y := by
    conv_lhs => rw [hy', (h y').map_sub, map_sum]
    simp [h1]
  have h3 : h y' y = h y y - ∑ a, c a * h (g a) y := by
    simp only [hy', map_sub, map_sum, map_smul, LinearMap.sub_apply, LinearMap.sum_apply,
      LinearMap.smul_apply, smul_eq_mul]
  have h4 : ∀ a, (σ (c a * h (g a) y)).re = ‖σ (h (g a) y)‖ ^ 2 / (σ (h (g a) (g a))).re := by
    intro a
    simp only [c]
    rw [map_mul, map_div₀, ← herm (g a) y, hσ, herm_real σ h hσ herm (g a)]
    set v := σ (h (g a) y) with hv
    set dd := (σ (h (g a) (g a))).re with hdd
    have e : star v * v = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
    have e2 : star v / (dd : ℂ) * v = ((‖v‖ ^ 2 / dd : ℝ) : ℂ) := by
      rw [div_mul_eq_mul_div, e]; push_cast; rfl
    rw [e2, Complex.ofReal_re]
    simp
  have h5 := hnn y'
  rw [h2, h3, map_sub, map_sum, Complex.sub_re, Complex.re_sum] at h5
  simp only [h4] at h5
  linarith

end DetK

theorem det_form_bound_field : Formalism.HermitianLatticeCounting.S6.DetBBoundK := by
  intro K U _ _ _ _ σ h η hσ herm hpos hη s u w
  have hnn : ∀ x : U, 0 ≤ (σ (h x x)).re := by
    intro x
    by_cases hx : x = 0
    · simp [hx]
    · exact (hpos x hx).le
  have haniso : ∀ x : U, h x x = 0 → x = 0 := by
    intro x hx
    by_contra h0
    have := hpos x h0
    rw [hx] at this
    simp at this
  obtain ⟨g, Lu, hLu, hu, hgo⟩ := gsK h herm haniso s u
  obtain ⟨g', Lw, hLw, hw, hgo'⟩ := gsK h herm haniso s w
  let β : U →ₗ[K] U →ₗ⋆[K] K := h.compl₂ (LinearMap.id - η)
  have hβ : ∀ x y, β x y = bEta h η x y := by intro x y; simp [β, bEta]
  have e1 : (Matrix.of fun a b => bEta h η (u a) (w b)).det =
      (Matrix.of fun a b => bEta h η (g a) (g' b)).det := by
    have := bmatK β g g' Lu Lw u w hu hw
    simp only [hβ] at this
    rw [this, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, hLu, hLw]; simp
  have e2 : ∀ (v gg : Fin s → U) (L : Matrix (Fin s) (Fin s) K), L.det = 1 →
      (∀ i, v i = ∑ k, L i k • gg k) → (∀ a b, a ≠ b → h (gg a) (gg b) = 0) →
      (Matrix.of fun a b => h (v a) (v b)).det = ∏ a, h (gg a) (gg a) := by
    intro v gg L hL hv ho
    rw [bmatK h gg gg L L v v hv hv, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, hL]
    have : (Matrix.of fun k l => h (gg k) (gg l)) = Matrix.diagonal (fun a => h (gg a) (gg a)) := by
      ext a b
      by_cases hab : a = b
      · subst hab; simp
      · simp [hab, ho a b hab]
    rw [this, Matrix.det_diagonal]; simp
  rw [e1, e2 u g Lu hLu hu hgo, e2 w g' Lw hLw hw hgo']
  have hn : ∀ gg : Fin s → U, ‖σ (∏ a, h (gg a) (gg a))‖ = ∏ a, (σ (h (gg a) (gg a))).re := by
    intro gg
    rw [map_prod, norm_prod]
    apply Finset.prod_congr rfl
    intro a _
    rw [herm_real σ h hσ herm (gg a), Complex.norm_real, Real.norm_of_nonneg (by simpa using hnn (gg a))]
    simp
  rw [hn, hn]
  set N : Matrix (Fin s) (Fin s) ℂ := Matrix.of fun a b => σ (bEta h η (g a) (g' b)) with hN
  have hdetN : σ (Matrix.of fun a b => bEta h η (g a) (g' b)).det = N.det := by
    rw [RingHom.map_det]; rfl
  rw [hdetN]
  have hP : 0 ≤ ∏ a, (σ (h (g a) (g a))).re := Finset.prod_nonneg (fun a _ => hnn _)
  have hP' : 0 ≤ ∏ a, (σ (h (g' a) (g' a))).re := Finset.prod_nonneg (fun a _ => hnn _)
  apply le_of_pow_le_pow_left₀ two_ne_zero (by positivity)
  rw [mul_pow, mul_pow, Real.sq_sqrt hP, Real.sq_sqrt hP']
  by_cases hz : ∃ a, g a = 0
  · obtain ⟨a, ha⟩ := hz
    have : N.det = 0 := Matrix.det_eq_zero_of_row_eq_zero a (by intro b; simp [hN, ha, bEta])
    rw [this]; simp; positivity
  · have hz : ∀ a, g a ≠ 0 := fun a ha => hz ⟨a, ha⟩
    have hdpos : ∀ a, 0 < (σ (h (g a) (g a))).re := fun a => hpos _ (hz a)
    have hd0 : ∀ a, h (g a) (g a) ≠ 0 := fun a h0 => hz a (haniso _ h0)
    set N' : Matrix (Fin s) (Fin s) ℂ :=
      Matrix.diagonal (fun a => (((Real.sqrt (σ (h (g a) (g a))).re)⁻¹ : ℝ) : ℂ)) * N with hN'
    have hNN : ‖N.det‖ ^ 2 = ‖N'.det‖ ^ 2 * ∏ a, (σ (h (g a) (g a))).re := by
      rw [hN', Matrix.det_mul, Matrix.det_diagonal, norm_mul, mul_pow, norm_prod, ← Finset.prod_pow]
      have : (∏ a, ‖(((Real.sqrt (σ (h (g a) (g a))).re)⁻¹ : ℝ) : ℂ)‖ ^ 2) * ∏ a, (σ (h (g a) (g a))).re = 1 := by
        rw [← Finset.prod_mul_distrib]
        apply Finset.prod_eq_one
        intro a _
        rw [Complex.norm_real, Real.norm_of_nonneg (by positivity), inv_pow, Real.sq_sqrt (hdpos a).le,
          inv_mul_cancel₀ (hdpos a).ne']
      calc ‖N.det‖ ^ 2 = ‖N.det‖ ^ 2 * 1 := by ring
        _ = _ := by rw [← this]; ring
    have hpar : ∀ x : U, (σ (h (x - η x) (x - η x))).re ≤ 4 * (σ (h x x)).re := by
      intro x
      have e : h (x - η x) (x - η x) + h (x + η x) (x + η x) = 4 * h x x := by
        simp only [map_sub, map_add, LinearMap.sub_apply, LinearMap.add_apply, hη]
        ring
      have h1 : (σ (h (x - η x) (x - η x) + h (x + η x) (x + η x))).re = (σ (4 * h x x)).re := by rw [e]
      rw [σ.map_add, σ.map_mul, Complex.add_re] at h1
      have h2 : (σ 4 * σ (h x x)).re = 4 * (σ (h x x)).re := by
        have : σ 4 = ((4:ℝ) : ℂ) := by
          rw [map_ofNat]; norm_num
        rw [this, Complex.re_ofReal_mul]
      rw [h2] at h1
      have := hnn (x + η x)
      linarith
    have hH := Formalism.HadamardInequality.P.hadamard_inequality_holds s N'ᵀ
    rw [Matrix.det_transpose] at hH
    have hrow : ∀ b, ∑ a, ‖N'ᵀ b a‖ ^ 2 ≤ 4 * (σ (h (g' b) (g' b))).re := by
      intro b
      refine le_trans (le_of_eq ?_) (le_trans
        (besselK σ h hσ herm hnn g hgo hd0 (g' b - η (g' b))) (hpar (g' b)))
      apply Finset.sum_congr rfl
      intro a _
      rw [Matrix.transpose_apply, hN', Matrix.diagonal_mul, norm_mul, mul_pow, Complex.norm_real,
        Real.norm_of_nonneg (by positivity), inv_pow, Real.sq_sqrt (hdpos a).le, hN]
      simp only [Matrix.of_apply, bEta]
      rw [inv_mul_eq_div]
    have hfin : ‖N'.det‖ ^ 2 ≤ (2 ^ s) ^ 2 * ∏ a, (σ (h (g' a) (g' a))).re := by
      refine le_trans hH ?_
      calc ∏ b, ∑ a, ‖N'ᵀ b a‖ ^ 2 ≤ ∏ b, (4 * (σ (h (g' b) (g' b))).re) :=
            Finset.prod_le_prod (fun b _ => Finset.sum_nonneg (fun a _ => by positivity)) (fun b _ => hrow b)
        _ = (2 ^ s) ^ 2 * ∏ a, (σ (h (g' a) (g' a))).re := by
            rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul,
              mul_comm s 2, pow_mul]
            norm_num
    rw [hNN]
    calc ‖N'.det‖ ^ 2 * ∏ a, (σ (h (g a) (g a))).re
        ≤ ((2 ^ s) ^ 2 * ∏ a, (σ (h (g' a) (g' a))).re) * ∏ a, (σ (h (g a) (g a))).re :=
          mul_le_mul_of_nonneg_right hfin hP
      _ = _ := by ring

theorem autBound_of_minkowskiBound (hM : Formalism.HermitianLatticeCounting.S6.MinkowskiBound) : Formalism.HermitianLatticeCounting.S6.AutBound :=
  automorphism_bound_of_hyp hM minkowski_number_dvd_factorial

end Formalism.HermitianLatticeCounting.P
