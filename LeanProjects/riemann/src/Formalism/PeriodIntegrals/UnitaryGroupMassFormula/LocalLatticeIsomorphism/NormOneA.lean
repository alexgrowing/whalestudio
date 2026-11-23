import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalLatticeIsomorphism.LatticeFromNormOne

noncomputable section
open scoped BigOperators
open NumberField

namespace PI.KLW.NO

theorem mem_O_iff {K : Type} [Field K] [NumberField K] {x : K} :
    x ∈ (algebraMap (𝓞 K) K).range ↔ IsIntegral ℤ x := by
  constructor
  · rintro ⟨y, rfl⟩; exact RingOfIntegers.isIntegral_coe y
  · intro h; exact ⟨⟨x, h⟩, rfl⟩

theorem c_mem_O {K : Type} [Field K] [NumberField K] (c : K →+* K) {x : K}
    (hx : x ∈ (algebraMap (𝓞 K) K).range) : c x ∈ (algebraMap (𝓞 K) K).range :=
  mem_O_iff.2 (map_isIntegral_int c (mem_O_iff.1 hx))

theorem natCast_mem_O {K : Type} [Field K] [NumberField K] (n : ℕ) :
    (n : K) ∈ (algebraMap (𝓞 K) K).range := ⟨(n : 𝓞 K), by simp⟩

theorem intCast_mem_O {K : Type} [Field K] [NumberField K] (n : ℤ) :
    (n : K) ∈ (algebraMap (𝓞 K) K).range := ⟨(n : 𝓞 K), by simp⟩

section Rp
variable {K : Type} [Field K] [NumberField K] {p : ℕ}

theorem rp_of_O {x : K} (hx : x ∈ (algebraMap (𝓞 K) K).range) : Rp K p x :=
  ⟨1, Nat.coprime_one_left _, by simpa using hx⟩

theorem rp_add {x y : K} (hx : Rp K p x) (hy : Rp K p y) : Rp K p (x + y) := by
  obtain ⟨s, hs, hsx⟩ := hx
  obtain ⟨t, ht, hty⟩ := hy
  refine ⟨s * t, Nat.Coprime.mul_left hs ht, ?_⟩
  have : ((s * t : ℕ) : K) * (x + y) = (t : K) * ((s : K) * x) + (s : K) * ((t : K) * y) := by
    push_cast; ring
  rw [this]
  exact Subring.add_mem _ (Subring.mul_mem _ (natCast_mem_O t) hsx)
    (Subring.mul_mem _ (natCast_mem_O s) hty)

theorem rp_mul {x y : K} (hx : Rp K p x) (hy : Rp K p y) : Rp K p (x * y) := by
  obtain ⟨s, hs, hsx⟩ := hx
  obtain ⟨t, ht, hty⟩ := hy
  refine ⟨s * t, Nat.Coprime.mul_left hs ht, ?_⟩
  have : ((s * t : ℕ) : K) * (x * y) = ((s : K) * x) * ((t : K) * y) := by push_cast; ring
  rw [this]
  exact Subring.mul_mem _ hsx hty

theorem rp_neg {x : K} (hx : Rp K p x) : Rp K p (-x) := by
  obtain ⟨s, hs, hsx⟩ := hx
  exact ⟨s, hs, by rw [mul_neg]; exact Subring.neg_mem _ hsx⟩

theorem rp_sub {x y : K} (hx : Rp K p x) (hy : Rp K p y) : Rp K p (x - y) := by
  rw [sub_eq_add_neg]; exact rp_add hx (rp_neg hy)

theorem rp_natCast (n : ℕ) : Rp K p (n : K) := rp_of_O (natCast_mem_O n)
theorem rp_one : Rp K p (1 : K) := by simpa using rp_natCast (K := K) (p := p) 1

theorem rp_pow {x : K} (hx : Rp K p x) (n : ℕ) : Rp K p (x ^ n) := by
  induction n with
  | zero => simpa using rp_one
  | succ n ih => rw [pow_succ]; exact rp_mul ih hx

theorem rp_c (c : K →+* K) {x : K} (hx : Rp K p x) : Rp K p (c x) := by
  obtain ⟨s, hs, hsx⟩ := hx
  refine ⟨s, hs, ?_⟩
  have : (s : K) * c x = c ((s : K) * x) := by rw [map_mul, map_natCast]
  rw [this]; exact c_mem_O c hsx

end Rp

theorem fixed_rat {K : Type} [Field K] [NumberField K] (c : K →+* K) (hK : Module.finrank ℚ K = 2)
    (hne : ∃ z, c z ≠ z) {x : K} (hx : c x = x) : ∃ q : ℚ, x = (q : K) := by
  by_contra hq
  push Not at hq
  have hli : LinearIndependent ℚ ![(1 : K), x] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · subst ht
      simp at hst
      exact ⟨hst, rfl⟩
    · exfalso
      apply hq (-s / t)
      rw [Rat.smul_def, Rat.smul_def] at hst
      have ht' : (t : K) ≠ 0 := by exact_mod_cast ht
      push_cast
      field_simp
      linear_combination hst
  let b := basisOfLinearIndependentOfCardEqFinrank hli (by simp [hK])
  obtain ⟨z, hz⟩ := hne
  apply hz
  rw [← b.sum_repr z]
  simp only [b, coe_basisOfLinearIndependentOfCardEqFinrank, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Rat.smul_def, map_add, map_mul, map_ratCast, map_one, hx]

theorem int_of_rat {K : Type} [Field K] [NumberField K] (q : ℚ)
    (h : (q : K) ∈ (algebraMap (𝓞 K) K).range) : ∃ m : ℤ, q = m := by
  have h1 : IsIntegral ℤ (algebraMap ℚ K q) := by
    rw [eq_ratCast]; exact mem_O_iff.1 h
  rw [isIntegral_algebraMap_iff (algebraMap ℚ K).injective] at h1
  obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.1 h1
  exact ⟨m, by rw [← hm]; simp⟩

theorem fixed_int {K : Type} [Field K] [NumberField K] (c : K →+* K) (hK : Module.finrank ℚ K = 2)
    (hne : ∃ z, c z ≠ z) {x : K} (hx : c x = x) (hO : x ∈ (algebraMap (𝓞 K) K).range) :
    ∃ m : ℤ, x = (m : K) := by
  obtain ⟨q, rfl⟩ := fixed_rat c hK hne hx
  obtain ⟨m, rfl⟩ := int_of_rat q hO
  exact ⟨m, by simp⟩

end PI.KLW.NO

namespace PI.KLW.NO

section Units
variable {K : Type} [Field K] [NumberField K] {p : ℕ}

theorem coprime_ne_zero (hp : p.Prime) {s : ℕ} (hs : Nat.Coprime s p) : s ≠ 0 := by
  rintro rfl
  exact hp.ne_one (by simpa using hs)

theorem not_rp_inv_p (hp : p.Prime) : ¬ Rp K p ((p : K)⁻¹) := by
  rintro ⟨s, hs, hsx⟩
  have h1 : (s : K) * (p : K)⁻¹ = (((s : ℚ) / p : ℚ) : K) := by push_cast; ring
  rw [h1] at hsx
  obtain ⟨m, hm⟩ := int_of_rat _ hsx
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have h2 : ((s : ℤ) : ℚ) = ((p * m : ℤ) : ℚ) := by
    push_cast; rw [← hm]; field_simp
  have h3 : (p : ℤ) ∣ (s : ℤ) := ⟨m, Int.cast_injective h2⟩
  have h4 : p ∣ s := Int.natCast_dvd_natCast.1 h3
  exact hp.ne_one (Nat.Coprime.eq_one_of_dvd hs.symm h4)

theorem rp_div_int {y : K} (hy : y ∈ (algebraMap (𝓞 K) K).range) {m : ℤ} (hm : ¬ (p : ℤ) ∣ m)
    (hp : p.Prime) : Rp K p (y / m) := by
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero _)
  have hmK : (m : K) ≠ 0 := by exact_mod_cast hm0
  have hcop : Nat.Coprime m.natAbs p :=
    ((Nat.Prime.coprime_iff_not_dvd hp).2 (by rwa [← Int.natCast_dvd])).symm
  refine ⟨m.natAbs, hcop, ?_⟩
  rcases Int.natAbs_eq m with h | h
  · have e : (m : K) = (m.natAbs : K) := by rw [← Int.cast_natCast]; exact congrArg _ h
    rw [← e, mul_div_cancel₀ _ hmK]; exact hy
  · have e : (m : K) = -(m.natAbs : K) := by rw [← Int.cast_natCast, ← Int.cast_neg]; exact congrArg _ h
    have e2 : (m.natAbs : K) = -(m : K) := by rw [e]; ring
    rw [e2, neg_mul, mul_div_cancel₀ _ hmK]; exact Subring.neg_mem _ hy

theorem inv_of_fixed (c : K →+* K) (hK : Module.finrank ℚ K = 2) (hne : ∃ z, c z ≠ z) (hp : p.Prime)
    {x : K} (hx : Rp K p x) (hfix : c x = x) (hnp : ¬ Rp K p (x / p)) : x ≠ 0 ∧ Rp K p x⁻¹ := by
  obtain ⟨s, hs, hsx⟩ := hx
  have hs0 : (s : K) ≠ 0 := by exact_mod_cast coprime_ne_zero hp hs
  have hfix' : c ((s : K) * x) = (s : K) * x := by rw [map_mul, map_natCast, hfix]
  obtain ⟨m, hm⟩ := fixed_int c hK hne hfix' hsx
  have hdvd : ¬ (p : ℤ) ∣ m := by
    rintro ⟨m', rfl⟩
    apply hnp
    refine ⟨s, hs, ?_⟩
    have hp0 : (p : K) ≠ 0 := by exact_mod_cast hp.ne_zero
    have : (s : K) * (x / p) = (m' : K) := by
      rw [mul_div_assoc', hm]; push_cast; field_simp
    rw [this]; exact intCast_mem_O m'
  have hm0 : m ≠ 0 := by rintro rfl; exact hdvd (dvd_zero _)
  have hmK : (m : K) ≠ 0 := by exact_mod_cast hm0
  have hx0 : x ≠ 0 := by
    rintro rfl; apply hmK; rw [← hm]; simp
  refine ⟨hx0, ?_⟩
  have : x⁻¹ = (s : K) / m := by rw [← hm]; field_simp
  rw [this]
  exact rp_div_int (natCast_mem_O s) hdvd hp

theorem unit_of_norm (c : K →+* K) (hc : ∀ x, c (c x) = x) (hK : Module.finrank ℚ K = 2)
    (hne : ∃ z, c z ≠ z) (hp : p.Prime) {z : K} (hz : Rp K p z) (hn : ¬ Rp K p (z * c z / p)) :
    z ≠ 0 ∧ Rp K p z⁻¹ := by
  have hfix : c (z * c z) = z * c z := by rw [map_mul, hc, mul_comm]
  obtain ⟨h0, hinv⟩ := inv_of_fixed c hK hne hp (rp_mul hz (rp_c c hz)) hfix hn
  have hz0 : z ≠ 0 := by rintro rfl; simp at h0
  have hcz0 : c z ≠ 0 := by rintro h; apply h0; rw [h, mul_zero]
  refine ⟨hz0, ?_⟩
  have : z⁻¹ = c z * (z * c z)⁻¹ := by field_simp
  rw [this]; exact rp_mul (rp_c c hz) hinv

theorem one_add_p_unit (c : K →+* K) (hc : ∀ x, c (c x) = x) (hK : Module.finrank ℚ K = 2)
    (hne : ∃ z, c z ≠ z) (hp : p.Prime) {r : K} (hr : Rp K p r) :
    (1 + (p : K) * r) ≠ 0 ∧ Rp K p (1 + (p : K) * r)⁻¹ := by
  apply unit_of_norm c hc hK hne hp (rp_add rp_one (rp_mul (rp_natCast p) hr))
  intro h
  apply not_rp_inv_p (K := K) hp
  have hp0 : (p : K) ≠ 0 := by exact_mod_cast hp.ne_zero
  have e : (p : K)⁻¹ = (1 + (p : K) * r) * c (1 + (p : K) * r) / p
      - (r + c r + (p : K) * r * c r) := by
    simp only [map_add, map_one, map_mul, map_natCast]
    field_simp
    ring
  rw [e]
  exact rp_sub h (rp_add (rp_add hr (rp_c c hr)) (rp_mul (rp_mul (rp_natCast p) hr) (rp_c c hr)))

theorem dvd_pow_p (c : K →+* K) (hc : ∀ x, c (c x) = x) (hK : Module.finrank ℚ K = 2)
    (hne : ∃ z, c z ≠ z) (hp : p.Prime) {z : K} (hz : Rp K p z) (h0 : z ≠ 0) :
    ∃ J : ℕ, Rp K p ((p : K) ^ J / z) := by
  obtain ⟨s, hs, hsz⟩ := hz
  have hs0 : (s : K) ≠ 0 := by exact_mod_cast coprime_ne_zero hp hs
  set Y := (s : K) * z with hY
  have hY0 : Y ≠ 0 := mul_ne_zero hs0 h0
  have hcY0 : c Y ≠ 0 := by
    intro h; apply hY0; rw [← hc Y, h, map_zero]
  have hfix : c (Y * c Y) = Y * c Y := by rw [map_mul, hc, mul_comm]
  obtain ⟨m, hm⟩ := fixed_int c hK hne hfix (Subring.mul_mem _ hsz (c_mem_O c hsz))
  have hm0 : m ≠ 0 := by
    rintro rfl; apply mul_ne_zero hY0 hcY0; rw [hm]; simp
  obtain ⟨J, n', hn', hJ⟩ := Nat.exists_eq_pow_mul_and_not_dvd (Int.natAbs_ne_zero.2 hm0) p hp.ne_one
  refine ⟨J, n', ((Nat.Prime.coprime_iff_not_dvd hp).2 hn').symm, ?_⟩
  have hnK : (m.natAbs : K) = (p : K) ^ J * n' := by exact_mod_cast hJ
  rcases Int.natAbs_eq m with h | h
  · have e : (m : K) = (m.natAbs : K) := by rw [← Int.cast_natCast]; exact congrArg _ h
    have e1 : Y * c Y = (p : K) ^ J * n' := by rw [hm, e, hnK]
    have : (n' : K) * ((p : K) ^ J / z) = (s : K) * c Y := by
      rw [← mul_div_assoc, div_eq_iff h0]
      rw [hY] at e1 ⊢
      linear_combination -e1
    rw [this]; exact Subring.mul_mem _ (natCast_mem_O s) (c_mem_O c hsz)
  · have e : (m : K) = -(m.natAbs : K) := by rw [← Int.cast_natCast, ← Int.cast_neg]; exact congrArg _ h
    have e1 : Y * c Y = -((p : K) ^ J * n') := by rw [hm, e, hnK]
    have : (n' : K) * ((p : K) ^ J / z) = -((s : K) * c Y) := by
      rw [← mul_div_assoc, div_eq_iff h0]
      rw [hY] at e1 ⊢
      linear_combination e1
    rw [this]; exact Subring.neg_mem _ (Subring.mul_mem _ (natCast_mem_O s) (c_mem_O c hsz))

theorem rp_pow_div (hp : p.Prime) {Q : ℕ} (hQ : Q ≠ 0) {k : ℕ} (hk : Q ≤ k) :
    Rp K p ((p : K) ^ k / Q) := by
  obtain ⟨e, n', hn', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hQ p hp.ne_one
  have hn0 : n' ≠ 0 := by rintro rfl; simp at hQ
  have hek : e < k := by
    have h1 : p ^ e ≤ p ^ e * n' := Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hn0)
    have h2 : k < p ^ k := Nat.lt_pow_self hp.one_lt
    exact (Nat.pow_lt_pow_iff_right hp.one_lt).1 (by omega)
  refine ⟨n', ((Nat.Prime.coprime_iff_not_dvd hp).2 hn').symm, ?_⟩
  have hp0 : (p : K) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hn0K : (n' : K) ≠ 0 := by exact_mod_cast hn0
  have : (n' : K) * ((p : K) ^ k / ((p ^ e * n' : ℕ) : K)) = (p : K) ^ (k - e) := by
    push_cast
    rw [← Nat.sub_add_cancel hek.le, pow_add]
    field_simp
    simp
  rw [this]; exact Subring.pow_mem _ (natCast_mem_O p) _

end Units

end PI.KLW.NO

namespace PI.KLW.NO

theorem ne_of_split {K : Type} [Field K] [NumberField K] (c : K →+* K) {p : ℕ} (h : SplitK c p) :
    ∃ z, c z ≠ z := by
  obtain ⟨P, _, _, a, b, hab, _, hb⟩ := h
  refine ⟨(a : K), fun h' => hb ?_⟩
  have : a = b := RingOfIntegers.ext (h'.symm.trans hab)
  rw [← this]; assumption

theorem eps {K : Type} [Field K] [NumberField K] (c : K →+* K) (hc : ∀ x, c (c x) = x)
    (hK : Module.finrank ℚ K = 2) {p : ℕ} (hp : p.Prime) (hs : SplitK c p) (k : ℕ) :
    ∃ ε : K, Rp K p ε ∧ ε + c ε = 1 ∧ Rp K p (ε * c ε / (p : K) ^ k) := by
  have hne := ne_of_split c hs
  obtain ⟨P, hP, hpP, a, b, hab, ha, hb⟩ := hs
  have hBA : c (b : K) = (a : K) := by rw [← hab, hc]
  have hfix : c ((a : K) ^ (k + 1) + (b : K) ^ (k + 1)) = (a : K) ^ (k + 1) + (b : K) ^ (k + 1) := by
    rw [map_add, map_pow, map_pow, hab, hBA, add_comm]
  have hO : (a : K) ^ (k + 1) + (b : K) ^ (k + 1) ∈ (algebraMap (𝓞 K) K).range :=
    ⟨a ^ (k + 1) + b ^ (k + 1), by rw [map_add, map_pow, map_pow]⟩
  obtain ⟨m, hm⟩ := fixed_int c hK hne hfix hO
  have hdvd : ¬ (p : ℤ) ∣ m := by
    rintro ⟨m', hm'⟩
    apply hb
    have e : a ^ (k + 1) + b ^ (k + 1) = (p : 𝓞 K) * (m' : 𝓞 K) := by
      apply RingOfIntegers.coe_injective
      rw [map_add, map_pow, map_pow, map_mul, map_natCast, map_intCast]
      have : (m : K) = (p : K) * m' := by rw [hm']; push_cast; ring
      exact hm.trans this
    have h1 : a ^ (k + 1) + b ^ (k + 1) ∈ P := by rw [e]; exact P.mul_mem_right _ hpP
    have h2 : b ^ (k + 1) ∈ P :=
      (P.add_mem_iff_right (P.pow_mem_of_mem ha (k + 1) (Nat.succ_pos k))).1 h1
    exact hP.mem_of_pow_mem _ h2
  have hm0 : m ≠ 0 := by rintro rfl; exact hdvd (dvd_zero _)
  have hmK : (m : K) ≠ 0 := by exact_mod_cast hm0

  have hfixN : c ((a : K) * b) = (a : K) * b := by rw [map_mul, hab, hBA, mul_comm]
  have hON : (a : K) * b ∈ (algebraMap (𝓞 K) K).range := ⟨a * b, by rw [map_mul]⟩
  obtain ⟨n, hn⟩ := fixed_int c hK hne hfixN hON
  have hpn : (p : ℤ) ∣ n := by
    by_contra hnd
    have hcop : IsCoprime (p : ℤ) n := by
      rw [Int.isCoprime_iff_gcd_eq_one]
      have : Nat.Coprime p n.natAbs :=
        (Nat.Prime.coprime_iff_not_dvd hp).2 (by rwa [← Int.natCast_dvd])
      exact this
    obtain ⟨u, v, huv⟩ := hcop
    apply hP.ne_top
    rw [Ideal.eq_top_iff_one]
    have e : (1 : 𝓞 K) = (u : 𝓞 K) * (p : 𝓞 K) + (v : 𝓞 K) * (a * b) := by
      apply RingOfIntegers.coe_injective
      rw [map_one, map_add, map_mul, map_mul, map_mul, map_intCast, map_intCast, map_natCast]
      have : ((u * p + v * n : ℤ) : K) = 1 := by rw [huv]; simp
      rw [← this]; push_cast
      have hn' : algebraMap (𝓞 K) K a * algebraMap (𝓞 K) K b = (n : K) := hn
      rw [hn']
    rw [e]
    exact P.add_mem (P.mul_mem_left _ hpP) (P.mul_mem_left _ (P.mul_mem_right _ ha))
  obtain ⟨n₁, hn₁⟩ := hpn
  have hab' : (a : K) * b = (p : K) * n₁ := by rw [hn, hn₁]; push_cast; ring
  refine ⟨(b : K) ^ (k + 1) / m, rp_div_int ⟨b ^ (k + 1), by rw [map_pow]⟩ hdvd hp, ?_, ?_⟩
  · rw [map_div₀, map_pow, hBA, map_intCast, ← add_div, add_comm, hm, div_self hmK]
  · rw [map_div₀, map_pow, hBA, map_intCast]
    have hp0 : (p : K) ≠ 0 := by exact_mod_cast hp.ne_zero
    have e1 : (b : K) ^ (k + 1) * (a : K) ^ (k + 1) = (p : K) ^ k * ((p : K) * (n₁ : K) ^ (k + 1)) := by
      rw [← mul_pow, mul_comm (b : K), hab', mul_pow, pow_succ]; ring
    have e2 : (b : K) ^ (k + 1) / m * ((a : K) ^ (k + 1) / m) / (p : K) ^ k
        = ((p : K) * (n₁ : K) ^ (k + 1) / m) * (1 / m) := by
      rw [show (b : K) ^ (k + 1) / m * ((a : K) ^ (k + 1) / m) / (p : K) ^ k
          = ((b : K) ^ (k + 1) * (a : K) ^ (k + 1)) / (p : K) ^ k / (m * m) by ring, e1,
        mul_div_cancel_left₀ _ (pow_ne_zero _ hp0)]
      ring
    rw [e2]
    exact rp_mul (rp_div_int (Subring.mul_mem _ (natCast_mem_O p) (Subring.pow_mem _ (intCast_mem_O n₁) _)) hdvd hp)
      (rp_div_int (Subring.one_mem _) hdvd hp)

end PI.KLW.NO
