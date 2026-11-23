import Mathlib
import GroundTheory.GlobalFields.AnalyticClassNumber.QuadraticConductor
import GroundTheory.HeightsAndTheta.Theta.EisensteinZeta.MirabolicInduction.CfunOmStatements
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Theta

namespace QuadraticFieldArithmetic

open NumberField Module Polynomial

section Basis

variable {K : Type} [Field K] {d : ℕ} {x : K}

theorem not_mem_range_of_sq [CharZero K] [Algebra ℚ K] (hd : 0 < d) (hx : x ^ 2 = -(d : K))
    (q : ℚ) : algebraMap ℚ K q ≠ x := by
  intro h
  have h2 : ((q ^ 2 : ℚ) : K) = ((-(d : ℚ) : ℚ) : K) := by
    rw [Rat.cast_pow, ← eq_ratCast (algebraMap ℚ K), h, hx]
    push_cast; ring
  have h3 : q ^ 2 = -(d : ℚ) := Rat.cast_injective h2
  have h4 : (0 : ℚ) < d := by exact_mod_cast hd
  nlinarith [sq_nonneg q]

theorem linearIndependent_one_alt [CharZero K] [Algebra ℚ K] (hd : 0 < d) (hx : x ^ 2 = -(d : K)) :
    LinearIndependent ℚ ![(1 : K), x] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  by_cases ht : t = 0
  · subst ht
    simp only [zero_smul, add_zero] at hst
    exact ⟨(smul_eq_zero.mp hst).resolve_right one_ne_zero, rfl⟩
  · exfalso
    apply not_mem_range_of_sq hd hx (-s / t)
    have : t • x = -(s • (1 : K)) := eq_neg_of_add_eq_zero_right hst
    rw [Algebra.smul_def, Algebra.smul_def, mul_one] at this
    rw [map_div₀, map_neg, ← this]
    exact mul_div_cancel_left₀ x ((_root_.map_ne_zero _).mpr ht)

end Basis

section Quadratic

variable {K : Type} [Field K] [NumberField K] [Algebra.IsQuadraticExtension ℚ K] {d : ℕ} {x : K}

def basisQ (hd : 0 < d) (hx : x ^ 2 = -(d : K)) : Basis (Fin 2) ℚ K :=
  basisOfLinearIndependentOfCardEqFinrank (linearIndependent_one_alt hd hx)
    (by rw [Fintype.card_fin, Algebra.IsQuadraticExtension.finrank_eq_two ℚ K])

theorem exists_rat (hd : 0 < d) (hx : x ^ 2 = -(d : K)) (y : K) :
    ∃ a b : ℚ, y = algebraMap ℚ K a + algebraMap ℚ K b * x := by
  have h := (basisQ hd hx).sum_repr y
  rw [Fin.sum_univ_two] at h
  refine ⟨(basisQ hd hx).repr y 0, (basisQ hd hx).repr y 1, ?_⟩
  conv_lhs => rw [← h]
  simp [basisQ, Algebra.smul_def]

theorem conj_alt_bis (hd : 0 < d) (hx : x ^ 2 = -(d : K)) : GroundTheory.Global.Quadratic.conj K x = -x := by
  set c := GroundTheory.Global.Quadratic.conj K
  have h1 : (c x) ^ 2 = x ^ 2 := by rw [← map_pow, hx, map_neg, map_natCast]
  have h2 : (c x - x) * (c x + x) = 0 := by linear_combination h1
  rcases mul_eq_zero.mp h2 with h | h
  · exfalso
    apply GroundTheory.Global.Quadratic.conj_ne_one K
    refine AlgEquiv.ext fun y => ?_
    obtain ⟨a, b, rfl⟩ := exists_rat hd hx y
    rw [AlgEquiv.one_apply, map_add, map_mul, AlgEquiv.commutes, AlgEquiv.commutes,
      sub_eq_zero.mp h]
  · exact eq_neg_of_add_eq_zero_left h

theorem conj_apply (hd : 0 < d) (hx : x ^ 2 = -(d : K)) (a b : ℚ) :
    GroundTheory.Global.Quadratic.conj K (algebraMap ℚ K a + algebraMap ℚ K b * x) =
      algebraMap ℚ K a - algebraMap ℚ K b * x := by
  rw [map_add, map_mul, AlgEquiv.commutes, AlgEquiv.commutes, conj_alt_bis hd hx]
  ring

omit [Algebra.IsQuadraticExtension ℚ K] in

theorem exists_int_of_isIntegral (q : ℚ) (h : IsIntegral ℤ (algebraMap ℚ K q)) :
    ∃ n : ℤ, q = n := by
  have h' : IsIntegral ℤ q := (isIntegral_algebraMap_iff (algebraMap ℚ K).injective).mp h
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp h'
  exact ⟨n, by simpa using hn.symm⟩

theorem isIntegral_conj {y : K} (hy : IsIntegral ℤ y) :
    IsIntegral ℤ (GroundTheory.Global.Quadratic.conj K y) :=
  hy.map ((GroundTheory.Global.Quadratic.conj K).toAlgHom.restrictScalars ℤ)

omit [NumberField K] [Algebra.IsQuadraticExtension ℚ K] in
theorem isIntegral_alt (hx : x ^ 2 = -(d : K)) : IsIntegral ℤ x := by
  refine ⟨X ^ 2 + C (d : ℤ), monic_X_pow_add_C _ two_ne_zero, ?_⟩
  rw [← aeval_def]
  simp [hx]

theorem coords_of_isIntegral (hdp : d.Prime) (hx : x ^ 2 = -(d : K)) {a b : ℚ}
    (hy : IsIntegral ℤ (algebraMap ℚ K a + algebraMap ℚ K b * x)) :
    ∃ A B N : ℤ, 2 * a = A ∧ 2 * b = B ∧ A ^ 2 + d * B ^ 2 = 4 * N := by
  have hd : 0 < d := hdp.pos
  set y := algebraMap ℚ K a + algebraMap ℚ K b * x with hy_def
  have hc := isIntegral_conj hy
  rw [conj_apply hd hx] at hc
  have h2 : (2 : K) = algebraMap ℚ K 2 := (map_ofNat _ 2).symm
  have hdK : (d : K) = algebraMap ℚ K d := (map_natCast _ d).symm

  have htr : IsIntegral ℤ (algebraMap ℚ K (2 * a)) := by
    have e : algebraMap ℚ K (2 * a) =
        y + (algebraMap ℚ K a - algebraMap ℚ K b * x) := by
      rw [map_mul, ← h2, hy_def]; ring
    rw [e]; exact hy.add hc
  obtain ⟨A, hA⟩ := exists_int_of_isIntegral _ htr

  have hnm : IsIntegral ℤ (algebraMap ℚ K (a ^ 2 + d * b ^ 2)) := by
    have e : algebraMap ℚ K (a ^ 2 + d * b ^ 2) =
        y * (algebraMap ℚ K a - algebraMap ℚ K b * x) := by
      rw [map_add, map_mul, map_pow, map_pow, ← hdK, hy_def]
      linear_combination (algebraMap ℚ K b) ^ 2 * hx
    rw [e]; exact hy.mul hc
  obtain ⟨N, hN⟩ := exists_int_of_isIntegral _ hnm
  have hAK : algebraMap ℤ K A = algebraMap ℚ K (2 * a) := by
    rw [hA, eq_intCast, map_intCast]
  have h2y : IsIntegral ℤ (y + y - algebraMap ℤ K A) :=
    (hy.add hy).sub isIntegral_algebraMap

  have hk : IsIntegral ℤ (algebraMap ℚ K (-(d * (2 * b)))) := by
    have e : algebraMap ℚ K (-(d * (2 * b))) = (y + y - algebraMap ℤ K A) * x := by
      rw [hAK, hy_def, map_neg, map_mul, map_mul, map_mul, ← hdK, ← h2]
      linear_combination (-(2 : K) * algebraMap ℚ K b) * hx
    rw [e]; exact h2y.mul (isIntegral_alt hx)
  obtain ⟨k, hk'⟩ := exists_int_of_isIntegral _ hk

  have he : IsIntegral ℤ (algebraMap ℚ K (-(d * (2 * b) ^ 2))) := by
    have e : algebraMap ℚ K (-(d * (2 * b) ^ 2)) = (y + y - algebraMap ℤ K A) ^ 2 := by
      rw [hAK, hy_def, map_neg, map_mul, map_pow, map_mul, map_mul, ← hdK, ← h2]
      linear_combination (-(2 : K) ^ 2 * algebraMap ℚ K b ^ 2) * hx
    rw [e]; exact h2y.pow 2
  obtain ⟨e, he'⟩ := exists_int_of_isIntegral _ he

  have hke : (k : ℚ) ^ 2 = d * (-e) := by
    have h1 : (k : ℚ) = -(d * (2 * b)) := hk'.symm
    have h2 : (e : ℚ) = -(d * (2 * b) ^ 2) := he'.symm
    rw [h1, h2]; ring
  have hke' : k ^ 2 = d * (-e) := by exact_mod_cast hke
  have hdk : (d : ℤ) ∣ k := by
    have hp : Prime (d : ℤ) := Nat.prime_iff_prime_int.mp hdp
    exact hp.dvd_of_dvd_pow (n := 2) ⟨-e, hke'⟩
  obtain ⟨B, hB⟩ := hdk
  refine ⟨A, -B, N, hA, ?_, ?_⟩
  · have h1 : (k : ℚ) = -(d * (2 * b)) := hk'.symm
    rw [hB] at h1
    push_cast at h1
    have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
    push_cast
    have : (d : ℚ) * (2 * b) = d * (-B) := by linarith
    exact mul_left_cancel₀ hd0 this
  · have h1 : (k : ℚ) = -(d * (2 * b)) := hk'.symm
    rw [hB] at h1
    push_cast at h1
    have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
    have hb : 2 * b = -(B : ℚ) := by
      have : (d : ℚ) * (2 * b) = d * (-B) := by linarith
      exact mul_left_cancel₀ hd0 this
    have : ((A ^ 2 + d * (-B) ^ 2 : ℤ) : ℚ) = ((4 * N : ℤ) : ℚ) := by
      push_cast
      rw [← hA, ← hN]
      have : (B : ℚ) = -(2 * b) := by linarith
      rw [this]; ring
    exact_mod_cast this

end Quadratic

theorem parity_of_norm {d : ℕ} (hd4 : d % 4 = 3) {A B N : ℤ} (h : A ^ 2 + d * B ^ 2 = 4 * N) :
    ∃ m : ℤ, A = B + 2 * m := by
  have h4 : (A : ZMod 4) ^ 2 + 3 * (B : ZMod 4) ^ 2 = 0 := by
    have := congrArg (Int.cast : ℤ → ZMod 4) h
    push_cast at this
    have hd' : (d : ZMod 4) = 3 := by
      rw [← ZMod.natCast_mod, hd4]; rfl
    have h0 : (4 : ZMod 4) = 0 := rfl
    rw [h0, zero_mul, hd'] at this
    exact this
  have key : ∀ a b : ZMod 4, a ^ 2 + 3 * b ^ 2 = 0 → (a.val + b.val) % 2 = 0 := by decide
  have h2 := key _ _ h4
  have hA4 := ZMod.val_intCast (n := 4) A
  have hB4 := ZMod.val_intCast (n := 4) B
  refine ⟨(A - B) / 2, ?_⟩
  omega

section Integers

variable {K : Type} [Field K] [NumberField K] [Algebra.IsQuadraticExtension ℚ K] {d : ℕ} {x : K}

omit [Algebra.IsQuadraticExtension ℚ K] in

theorem isIntegral_omega (hd4 : d % 4 = 3) (hx : x ^ 2 = -(d : K)) :
    IsIntegral ℤ ((1 + x) / 2) := by
  refine ⟨X ^ 2 - X + C (((d + 1) / 4 : ℕ) : ℤ), ?_, ?_⟩
  · refine Monic.add_of_left (Monic.sub_of_left (monic_X_pow 2) ?_) ?_
    · rw [degree_X, degree_X_pow]; norm_num
    · refine lt_of_le_of_lt degree_C_le ?_
      rw [degree_sub_eq_left_of_degree_lt (by rw [degree_X, degree_X_pow]; norm_num), degree_X_pow]
      norm_num
  · rw [← aeval_def]
    have h4 : (((d + 1) / 4 : ℕ) : K) * 4 = d + 1 := by
      have e : (d + 1) / 4 * 4 = d + 1 := Nat.div_mul_cancel (by omega)
      calc (((d + 1) / 4 : ℕ) : K) * 4 = (((d + 1) / 4 * 4 : ℕ) : K) := by push_cast; ring
        _ = d + 1 := by rw [e]; push_cast; ring
    simp only [map_add, map_sub, map_pow, aeval_X, map_natCast]
    linear_combination (1 / 4 : K) * hx + (1 / 4 : K) * h4

def omega (hd4 : d % 4 = 3) (hx : x ^ 2 = -(d : K)) : 𝓞 K :=
  ⟨(1 + x) / 2, isIntegral_omega hd4 hx⟩

omit [Algebra.IsQuadraticExtension ℚ K] in
theorem coe_omega (hd4 : d % 4 = 3) (hx : x ^ 2 = -(d : K)) :
    ((omega hd4 hx : 𝓞 K) : K) = (1 + x) / 2 := rfl

theorem exists_int_coords (hdp : d.Prime) (hd4 : d % 4 = 3) (hx : x ^ 2 = -(d : K)) (y : 𝓞 K) :
    ∃ m n : ℤ, y = m • (1 : 𝓞 K) + n • omega hd4 hx := by
  obtain ⟨a, b, hab⟩ := exists_rat hdp.pos hx (y : K)
  have hy : IsIntegral ℤ (algebraMap ℚ K a + algebraMap ℚ K b * x) := hab ▸ y.2
  obtain ⟨A, B, N, hA, hB, hN⟩ := coords_of_isIntegral hdp hx hy
  obtain ⟨m, hm⟩ := parity_of_norm hd4 hN
  refine ⟨m, B, ?_⟩
  apply RingOfIntegers.ext
  rw [hab]
  change _ = algebraMap (𝓞 K) K (m • (1 : 𝓞 K) + B • omega hd4 hx)
  rw [map_add, map_zsmul, map_zsmul, map_one, ← RingOfIntegers.coe_eq_algebraMap, coe_omega,
    zsmul_eq_mul, zsmul_eq_mul]
  have ha : algebraMap ℚ K a = (A : K) / 2 := by
    rw [eq_div_iff two_ne_zero, ← map_intCast (algebraMap ℚ K), ← hA]; simp [mul_comm]
  have hb : algebraMap ℚ K b = (B : K) / 2 := by
    rw [eq_div_iff two_ne_zero, ← map_intCast (algebraMap ℚ K), ← hB]; simp [mul_comm]
  rw [ha, hb, hm]
  push_cast
  ring

theorem linearIndependent_one_omega (hd : 0 < d) (hd4 : d % 4 = 3) (hx : x ^ 2 = -(d : K)) :
    LinearIndependent ℤ ![(1 : 𝓞 K), omega hd4 hx] := by
  rw [LinearIndependent.pair_iff]
  intro m n hmn
  have h := congrArg (algebraMap (𝓞 K) K) hmn
  rw [map_add, map_zsmul, map_zsmul, map_one, map_zero, ← RingOfIntegers.coe_eq_algebraMap,
    coe_omega, zsmul_eq_mul, zsmul_eq_mul, mul_one] at h
  by_cases hn : n = 0
  · subst hn
    simp only [Int.cast_zero, zero_mul, add_zero, Int.cast_eq_zero] at h
    exact ⟨h, rfl⟩
  · exfalso
    apply not_mem_range_of_sq hd hx (-(2 * m + n) / n)
    have hn' : (n : K) ≠ 0 := Int.cast_ne_zero.mpr hn
    rw [map_div₀, map_neg, map_add, map_mul, map_intCast, map_intCast, map_ofNat]
    field_simp
    linear_combination (-2 : K) * h

def basisInt (hdp : d.Prime) (hd4 : d % 4 = 3) (hx : x ^ 2 = -(d : K)) : Basis (Fin 2) ℤ (𝓞 K) :=
  Basis.mk (linearIndependent_one_omega hdp.pos hd4 hx) (by
    rintro y -
    obtain ⟨m, n, rfl⟩ := exists_int_coords hdp hd4 hx y
    exact Submodule.add_mem _ (Submodule.smul_mem _ m (Submodule.subset_span ⟨0, rfl⟩))
      (Submodule.smul_mem _ n (Submodule.subset_span ⟨1, rfl⟩)))

theorem basisInt_apply (hdp : d.Prime) (hd4 : d % 4 = 3) (hx : x ^ 2 = -(d : K)) :
    ⇑(basisInt hdp hd4 hx) = ![1, omega hd4 hx] := by
  simp [basisInt]

theorem trace_eq_of (y : K) (q : ℚ) (h : y + GroundTheory.Global.Quadratic.conj K y = algebraMap ℚ K q) :
    Algebra.trace ℚ K y = q :=
  (algebraMap ℚ K).injective (by rw [GroundTheory.Global.Quadratic.algebraMap_trace, h])

theorem discr_eq (hdp : d.Prime) (hd4 : d % 4 = 3) (hx : x ^ 2 = -(d : K)) :
    discr K = -(d : ℤ) := by
  have hd := hdp.pos
  set b := basisInt hdp hd4 hx
  have h1 : (discr K : ℚ) = Algebra.discr ℚ (b.localizationLocalization ℚ (nonZeroDivisors ℤ) K) := by
    rw [Algebra.discr_localizationLocalization, discr_eq_discr]; rfl
  have hb : ⇑(b.localizationLocalization ℚ (nonZeroDivisors ℤ) K) = ![(1 : K), (1 + x) / 2] := by
    ext i
    rw [Basis.localizationLocalization_apply, basisInt_apply]
    fin_cases i <;> simp [coe_omega]
  rw [hb, Algebra.discr_def, Matrix.det_fin_two] at h1
  simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, one_mul, mul_one] at h1
  have c := conj_alt_bis (K := K) hd hx
  have t1 : Algebra.trace ℚ K 1 = 2 := trace_eq_of _ _ (by rw [map_one, map_ofNat]; norm_num)
  have tω : Algebra.trace ℚ K ((1 + x) / 2) = 1 :=
    trace_eq_of _ _ (by rw [map_div₀, map_add, map_one, c, map_one, map_ofNat]; ring)
  have tω2 : Algebra.trace ℚ K ((1 + x) / 2 * ((1 + x) / 2)) = (1 - d) / 2 :=
    trace_eq_of _ _ (by
      rw [map_mul, map_div₀, map_add, map_one, c, map_ofNat, map_div₀, map_sub, map_one,
        map_natCast, map_ofNat]
      linear_combination (1 / 2 : K) * hx)
  rw [t1, tω, tω2] at h1
  have : (discr K : ℚ) = ((-(d : ℤ) : ℤ) : ℚ) := by rw [h1]; push_cast; ring
  exact_mod_cast this

end Integers

section Units

variable {K : Type} [Field K] [NumberField K] [Algebra.IsQuadraticExtension ℚ K] {d : ℕ} {x : K}

theorem eq_one_or_neg_one_of_mem_torsion (hdp : d.Prime) (hd7 : 4 < d) (hx : x ^ 2 = -(d : K))
    {u : (𝓞 K)ˣ} (hu : u ∈ Units.torsion K) : u = 1 ∨ u = -1 := by
  have hd := hdp.pos
  obtain ⟨n, hn, hun⟩ := isOfFinOrder_iff_pow_eq_one.mp ((CommGroup.mem_torsion u).mp hu)
  set y : K := (((u : 𝓞 K)) : K) with hy
  have hyn : y ^ n = 1 := by
    show algebraMap (𝓞 K) K (u : 𝓞 K) ^ n = 1
    rw [← map_pow, ← Units.val_pow_eq_pow_val, hun, Units.val_one, map_one]
  obtain ⟨a, b, hab⟩ := exists_rat hd hx y
  have hint : IsIntegral ℤ (algebraMap ℚ K a + algebraMap ℚ K b * x) := hab ▸ (u : 𝓞 K).2
  obtain ⟨A, B, N, hA, hB, -⟩ := coords_of_isIntegral hdp hx hint
  set c := GroundTheory.Global.Quadratic.conj K
  have hnorm : algebraMap ℚ K (a ^ 2 + d * b ^ 2) = y * c y := by
    rw [hab, conj_apply hd hx, map_add, map_mul, map_pow, map_pow, map_natCast]
    linear_combination (algebraMap ℚ K b) ^ 2 * hx
  have h1 : (a ^ 2 + d * b ^ 2) ^ n = 1 := by
    apply (algebraMap ℚ K).injective
    rw [map_pow, hnorm, mul_pow, hyn, ← map_pow, hyn, map_one, one_mul, map_one]
  have h0 : 0 ≤ a ^ 2 + d * b ^ 2 := by positivity
  have h2 : a ^ 2 + d * b ^ 2 = 1 := (pow_eq_one_iff_of_nonneg h0 hn.ne').mp h1
  have h3 : A ^ 2 + d * B ^ 2 = 4 := by
    have : ((A ^ 2 + d * B ^ 2 : ℤ) : ℚ) = ((4 : ℤ) : ℚ) := by
      push_cast
      rw [← hA, ← hB]
      linear_combination 4 * h2
    exact_mod_cast this
  have hB0 : B = 0 := by
    by_contra hB0
    have hB1 : 1 ≤ B ^ 2 := by
      have := Int.one_le_abs hB0
      nlinarith [sq_abs B]
    have hd' : (5 : ℤ) ≤ d := by exact_mod_cast hd7
    nlinarith [sq_nonneg A]
  rw [hB0] at h3
  have hA2 : A = 2 ∨ A = -2 := by
    have : (A - 2) * (A + 2) = 0 := by linear_combination h3
    rcases mul_eq_zero.mp this with h | h
    · left; linarith
    · right; linarith
  have hb : b = 0 := by
    have : (2 : ℚ) * b = 0 := by rw [hB, hB0]; simp
    linarith
  rcases hA2 with hA2 | hA2
  · left
    have ha : a = 1 := by
      have : (2 : ℚ) * a = 2 := by rw [hA, hA2]; simp
      linarith
    apply Units.ext
    apply RingOfIntegers.ext
    show y = _
    rw [hab, ha, hb]; simp
  · right
    have ha : a = -1 := by
      have : (2 : ℚ) * a = -2 := by rw [hA, hA2]; simp
      linarith
    apply Units.ext
    apply RingOfIntegers.ext
    show y = _
    rw [hab, ha, hb]; simp

theorem torsionOrder_eq_two (hdp : d.Prime) (hd7 : 4 < d) (hx : x ^ 2 = -(d : K)) :
    Units.torsionOrder K = 2 := by
  have hneg : (-1 : (𝓞 K)ˣ) ∈ Units.torsion K :=
    (CommGroup.mem_torsion _).mpr (isOfFinOrder_iff_pow_eq_one.mpr ⟨2, two_pos, by simp⟩)
  rw [Units.torsionOrder, Nat.card_eq_two_iff]
  refine ⟨1, ⟨-1, hneg⟩, ?_, ?_⟩
  · intro h
    have h' := congrArg (fun v : Units.torsion K => (((v : (𝓞 K)ˣ) : 𝓞 K) : K)) h
    simp only [OneMemClass.coe_one, Units.val_one, Units.val_neg] at h'
    have : ((1 : 𝓞 K) : K) = ((-1 : 𝓞 K) : K) := h'
    rw [RingOfIntegers.coe_eq_algebraMap, RingOfIntegers.coe_eq_algebraMap, map_one, map_neg,
      map_one] at this
    norm_num at this
  · ext v
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    rcases eq_one_or_neg_one_of_mem_torsion hdp hd7 hx v.2 with h | h
    · left; exact Subtype.ext h
    · right; exact Subtype.ext h

end Units

section Embeddings

variable {K : Type} [Field K] {d : ℕ} {x : K}

theorem im_ne_zero (hd : 0 < d) (hx : x ^ 2 = -(d : K)) (σ : K →+* ℂ) : (σ x).im ≠ 0 := by
  intro h
  have h2 : (σ x) ^ 2 = -(d : ℂ) := by rw [← map_pow, hx, map_neg, map_natCast]
  have h3 := congrArg Complex.re h2
  rw [sq, Complex.mul_re, h, mul_zero, sub_zero] at h3
  have h4 : (0 : ℝ) < d := by exact_mod_cast hd
  simp only [Complex.neg_re, Complex.natCast_re] at h3
  nlinarith [mul_self_nonneg (σ x).re]

theorem exists_im_ne_zero (hd : 0 < d) (hx : x ^ 2 = -(d : K)) (σ : K →+* ℂ) :
    ∃ y : K, (σ y).im ≠ 0 :=
  ⟨x, im_ne_zero hd hx σ⟩

end Embeddings

section Character

theorem legendreSym_neg_eq {p d : ℕ} [Fact p.Prime] [Fact d.Prime] (hp2 : p ≠ 2) (hd4 : d % 4 = 3) :
    legendreSym p (-(d : ℤ)) = legendreSym d p := by
  have hd2 : d ≠ 2 := by omega
  rw [neg_eq_neg_one_mul, legendreSym.mul p (-1) d, legendreSym.at_neg_one hp2,
    legendreSym.quadratic_reciprocity' hd2 hp2]
  have hpo : p % 2 = 1 := Nat.odd_iff.mp ((Fact.out : p.Prime).odd_of_ne_two hp2)
  have hd' : (d / 2) % 2 = 1 := by omega
  rcases Nat.odd_mod_four_iff.mp hpo with h | h
  · rw [ZMod.χ₄_nat_one_mod_four h]
    have he : Even (d / 2 * (p / 2)) := by
      rw [Nat.even_mul]; right; rw [Nat.even_iff]; omega
    rw [he.neg_one_pow]; ring
  · rw [ZMod.χ₄_nat_three_mod_four h]
    have ho : Odd (d / 2 * (p / 2)) := by
      rw [Nat.odd_mul, Nat.odd_iff, Nat.odd_iff]; omega
    rw [ho.neg_one_pow]; ring

variable {K : Type} [Field K] [NumberField K] [Algebra.IsQuadraticExtension ℚ K] {d : ℕ} {x : K}

theorem LFunction_kronecker_eq [hdf : Fact d.Prime] (hd4 : d % 4 = 3) (hx : x ^ 2 = -(d : K))
    (s : ℂ) :
    DirichletCharacter.LFunction (GroundTheory.Global.Quadratic.kronecker K) s =
      DirichletCharacter.LFunction (legendreCharacter d) s := by
  have hdisc := discr_eq hdf.out hd4 hx
  have hD : (discr K).natAbs = d := by rw [hdisc]; simp
  have : NeZero d := ⟨hdf.out.ne_zero⟩
  rw [← GroundTheory.Global.Quadratic.LFunction_kroneckerChar K s,
    ← GroundTheory.Global.Quadratic.LFunction_changeLevel_of_eq hD]
  congr 1
  refine MulChar.ext fun a => ?_
  obtain ⟨p, hp_gt, hpp, hpa⟩ := Nat.forall_exists_prime_gt_and_eq_mod a.isUnit (2 * d)
  have := Fact.mk hpp
  have hp2 : p ≠ 2 := by omega
  rw [← hpa, GroundTheory.Global.Quadratic.changeLevel_of_eq_apply hD,
    GroundTheory.Global.Quadratic.kroneckerChar_apply_prime K p hp2, hdisc, legendreSym_neg_eq hp2 hd4]
  simp [legendreCharacter, MulChar.ringHomComp_apply, legendreSym]

end Character

end QuadraticFieldArithmetic

end GroundTheory.Heights₂.Theta
