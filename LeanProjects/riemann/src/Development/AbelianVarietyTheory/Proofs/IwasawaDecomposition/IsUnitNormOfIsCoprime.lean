import Mathlib
import Formalism.LocalRingCardinality.DataHost
import Formalism.FrobeniusOrbits.HostCorollaries
open NumberField IsDedekindDomain

namespace GlobalTheory.NormSquareRamified

theorem dvd_of_mul_sq {p : ℕ} (hp : p.Prime) {q D : ℤ} (hq : ¬ (p : ℤ) ∣ q) (B : ℚ)
    (h : ((q * p : ℤ) : ℚ) * B ^ 2 = D) : (p : ℤ) ∣ D := by
  have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  by_contra hD
  have hden : (B.den : ℚ) ≠ 0 := by exact_mod_cast B.den_nz
  have h1 : q * p * B.num ^ 2 = D * (B.den : ℤ) ^ 2 := by
    have hB : (B.num : ℚ) = B * B.den := by
      rw [Rat.mul_den_eq_num]
    have : ((q * p * B.num ^ 2 : ℤ) : ℚ) = ((D * (B.den : ℤ) ^ 2 : ℤ) : ℚ) := by
      push_cast at h ⊢
      rw [hB, ← h]; ring
    exact_mod_cast this
  have h2 : (p : ℤ) ∣ (B.den : ℤ) := by
    have : (p : ℤ) ∣ D * (B.den : ℤ) ^ 2 := ⟨q * B.num ^ 2, by rw [← h1]; ring⟩
    exact hpp.dvd_of_dvd_pow ((hpp.dvd_or_dvd this).resolve_left hD)
  obtain ⟨c, hc⟩ := h2
  have h3 : q * B.num ^ 2 = p * (D * c ^ 2) := by
    apply mul_left_cancel₀ hpp.ne_zero
    rw [hc] at h1
    linear_combination h1
  have h4 : (p : ℤ) ∣ B.num :=
    hpp.dvd_of_dvd_pow ((hpp.dvd_or_dvd ⟨_, h3⟩).resolve_left hq)
  have h5 : IsCoprime B.num (B.den : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    simpa [Int.gcd] using B.reduced
  exact hpp.not_isUnit (h5.isUnit_of_dvd' h4 ⟨c, hc⟩)

theorem isUnit_norm_of_isCoprime {F : Type*} [Field F] [NumberField F] (n : ℕ) (y : 𝓞 F)
    (h : IsCoprime y (n : 𝓞 F)) : IsUnit ((Algebra.norm ℤ y : ℤ) : ZMod n) := by
  classical
  obtain ⟨u, v, huv⟩ := h
  let b := RingOfIntegers.basis F
  have h1 : u * y = 1 - (n : ℤ) • v := by
    rw [← huv]; simp [mul_comm]
  have h2 : ((Algebra.norm ℤ (u * y) : ℤ) : ZMod n) = 1 := by
    rw [Algebra.norm_eq_matrix_det b, h1, map_sub, map_one, map_zsmul]
    have := (Int.castRingHom (ZMod n)).map_det (1 - (n : ℤ) • Algebra.leftMulMatrix b v)
    rw [eq_intCast] at this
    rw [this, map_sub, map_one, map_zsmul]
    have h0 : (n : ℤ) • (Int.castRingHom (ZMod n)).mapMatrix (Algebra.leftMulMatrix b v) = 0 := by
      ext i j
      simp
    rw [h0, sub_zero, Matrix.det_one]
  rw [map_mul, Int.cast_mul, mul_comm] at h2
  exact IsUnit.of_mul_eq_one _ h2

theorem exists_sq_sub_norm {F : Type*} [Field F] [NumberField F] {p : ℕ} (hp : p.Prime) {q : ℤ}
    (hq : ¬ (p : ℤ) ∣ q) (s : F) (hs : s * s = ((q * p : ℤ) : F)) (y : 𝓞 F) :
    ∃ A : ℤ, (p : ℤ) ∣ A ^ 2 - 4 * Algebra.norm ℤ y := by
  have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  set m : ℚ := ((q * p : ℤ) : ℚ) with hm
  have hm0 : m ≠ 0 := by
    rw [hm, Int.cast_ne_zero]
    exact mul_ne_zero (fun h => hq (h ▸ dvd_zero _)) hpp.ne_zero
  have : Fact (∀ r : ℚ, r ^ 2 ≠ m + 0 * r) := ⟨fun r hr => by
    rw [zero_mul, add_zero] at hr
    have hr0 : r ≠ 0 := by
      rintro rfl
      exact hm0 (by rw [← hr]; simp)
    have : m * r⁻¹ ^ 2 = ((1 : ℤ) : ℚ) := by
      rw [← hr]; field_simp; simp
    exact hpp.not_dvd_one (dvd_of_mul_sq hp hq _ this)⟩
  let K := QuadraticAlgebra ℚ m 0
  let φ : K →ₐ[ℚ] F := QuadraticAlgebra.lift ⟨s, by
    rw [hs, zero_smul, add_zero, hm, Algebra.smul_def, mul_one, map_intCast]⟩
  let : Algebra K F := φ.toRingHom.toAlgebra
  have : IsScalarTower ℚ K F := IsScalarTower.of_algebraMap_eq fun x => (φ.commutes x).symm
  have : Module.Finite ℚ K := Module.Finite.of_basis (QuadraticAlgebra.basis m 0)
  set w : K := Algebra.norm K (y : F) with hw
  have hwi : IsIntegral ℤ w := Algebra.isIntegral_norm K y.isIntegral_coe
  have hn : ((Algebra.norm ℤ y : ℤ) : ℚ) = w.norm := by
    rw [Algebra.coe_norm_int, ← Algebra.norm_norm (S := K), ← hw,
      ← QuadraticAlgebra.det_toLinearMap_eq_norm, Algebra.norm_apply]
    rfl
  have hst : IsIntegral ℤ (star w) := hwi.map (starRingEnd K).toIntAlgHom
  have htr : IsIntegral ℤ (QuadraticAlgebra.trace w) := by
    have := hwi.add hst
    rw [← QuadraticAlgebra.algebraMap_trace_eq_add_star] at this
    exact (isIntegral_algebraMap_iff (algebraMap ℚ K).injective).mp this
  obtain ⟨A, hA⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).mp htr
  refine ⟨A, dvd_of_mul_sq hp hq (2 * w.im) ?_⟩
  rw [← hm]
  rw [eq_intCast] at hA
  push_cast
  rw [hA, hn, QuadraticAlgebra.trace_def, QuadraticAlgebra.norm_def]
  ring

theorem jacobiSym_norm_eq_one {F : Type*} [Field F] [NumberField F] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {q : ℤ} (hq : ¬ (p : ℤ) ∣ q) (s : F) (hs : s * s = ((q * p : ℤ) : F)) (y : 𝓞 F)
    (hy : IsCoprime y (p : 𝓞 F)) : jacobiSym (Algebra.norm ℤ y) p = 1 := by
  have := Fact.mk hp
  obtain ⟨A, hA⟩ := exists_sq_sub_norm hp hq s hs y
  have hu := isUnit_norm_of_isCoprime p y hy
  rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym.eq_one_iff p hu.ne_zero]
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at hA
  push_cast at hA
  refine ⟨(A : ZMod p) / 2, ?_⟩
  field_simp
  linear_combination -hA

theorem host_jacobiSym_norm : ∀ (R : Formalism.BasicNotions.Ranks) (H : Formalism.BasicNotions.Host R) (y : 𝓞 H.F),
    IsCoprime y ((H.d : ℕ) : 𝓞 H.F) → jacobiSym (Algebra.norm ℤ y) H.d = 1 := by
  intro R H y hy
  obtain ⟨hq, hd, hqd, -, hd2⟩ := H.hypOdd
  have hneg : ∀ (z : ℂ) (n : ℕ), 0 < n → z ^ 2 = -(n : ℂ) → star z = -z := by
    intro z n hn h
    have hr : (0 : ℝ) < n := by exact_mod_cast hn
    have h1 := congrArg Complex.re h
    have h2 := congrArg Complex.im h
    simp [sq, Complex.mul_re, Complex.mul_im] at h1 h2
    have hre : z.re = 0 := by
      have h3 : z.re * z.im = 0 := by linarith
      rcases mul_eq_zero.mp h3 with h4 | h4
      · exact h4
      · rw [h4] at h1; nlinarith [sq_nonneg z.re]
    apply Complex.ext <;> simp [hre]
  have hmem : H.sqq * H.sqd ∈ H.F := by
    intro φ
    have ha : star (φ H.sqq) = -φ H.sqq :=
      hneg _ H.q hq.pos (by rw [← map_pow, H.sqq_sq]; simp)
    have hb : star (φ H.sqd) = -φ H.sqd :=
      hneg _ H.d hd.pos (by rw [← map_pow, H.sqd_sq]; simp)
    rw [map_mul, star_mul, ha, hb]; ring
  refine jacobiSym_norm_eq_one hd hd2 (q := (H.q : ℤ)) ?_ ⟨_, hmem⟩ ?_ y hy
  · intro h
    exact hqd ((Nat.prime_dvd_prime_iff_eq hd hq).mp (by exact_mod_cast h)).symm
  · apply Subtype.ext
    change (H.sqq * H.sqd) * (H.sqq * H.sqd) = _
    have : (H.sqq * H.sqd) * (H.sqq * H.sqd) = H.sqq ^ 2 * H.sqd ^ 2 := by ring
    rw [this, H.sqq_sq, H.sqd_sq]
    push_cast
    ring

end GlobalTheory.NormSquareRamified
