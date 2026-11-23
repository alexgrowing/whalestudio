import Mathlib
import Formalism.LocalToGlobal.Columns.BaseHost
import Formalism.LocalToGlobal.Columns.NonDeg

open NumberField IsDedekindDomain Module IntermediateField

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Host Formalism.FrobeniusOrbits

section SplitGen

open Ideal

variable {E L : Type} [Field E] [NumberField E] [Field L] [NumberField L] [Algebra E L]

theorem not_dvd_of_modEq_one {N p : ℕ} (hN : 0 < N) (hp : p.Prime) (hpN : p ≡ 1 [MOD N]) : ¬ p ∣ N := by
  intro h
  have h1 : N ∣ p - 1 := (Nat.modEq_iff_dvd' hp.one_lt.le).1 hpN.symm
  have h2 : N ≤ p - 1 := Nat.le_of_dvd (by have := hp.one_lt; omega) h1
  have h3 : p ≤ N := Nat.le_of_dvd hN h
  have := hp.one_lt
  omega

theorem split_of_modEq_one_cyclotomic (L : Type) [Field L] [NumberField L] [Algebra E L] (N : ℕ) [NeZero N] [IsCyclotomicExtension {N} ℚ L]
    {p : ℕ} (hp : p.Prime) (hpN : p ≡ 1 [MOD N])
    (P : Ideal (𝓞 E)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})] :
    P.inertiaDeg ℤ = 1 ∧ P.ramificationIdx ℤ = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨⟨Q, hQ1, hQ2⟩⟩ := P.nonempty_primesOver (S := 𝓞 L)
  have := hQ1
  have := hQ2
  have : Q.LiesOver (span {(p : ℤ)}) := LiesOver.trans Q P _
  have hnd : ¬ p ∣ N := not_dvd_of_modEq_one (NeZero.pos N) hp hpN
  have h1 := IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd p L Q hnd
  have h2 := IsCyclotomicExtension.Rat.ramificationIdx_eq_of_not_dvd p L Q hnd
  have h3 : orderOf (p : ZMod N) = 1 := by
    rw [orderOf_eq_one_iff]
    have := (ZMod.natCast_eq_natCast_iff p 1 N).2 hpN
    rwa [Nat.cast_one] at this
  rw [h3] at h1
  have h4 := inertiaDeg_below_dvd (R := ℤ) P Q
  have h5 := ramificationIdx_below_dvd (R := ℤ) P Q
  rw [h1] at h4
  rw [h2] at h5
  exact ⟨Nat.dvd_one.1 h4, Nat.dvd_one.1 h5⟩

theorem liesOver_span_of_natCast_mem_columns {p : ℕ} (hp : p.Prime) (P : Ideal (𝓞 E)) [P.IsPrime] (h : (p : 𝓞 E) ∈ P) :
    P.LiesOver (span {(p : ℤ)}) := by
  have : Fact p.Prime := ⟨hp⟩
  rw [liesOver_iff]
  refine IsMaximal.eq_of_le (Int.ideal_span_isMaximal_of_prime p) IsPrime.ne_top' ?_
  rw [span_singleton_le_iff_mem, mem_comap, algebraMap_int_eq, map_natCast]
  exact h

theorem natCast_mem_of_liesOver_span {p : ℕ} (P : Ideal (𝓞 E)) [h : P.LiesOver (span {(p : ℤ)})] : (p : 𝓞 E) ∈ P := by
  have h1 : (p : ℤ) ∈ P.under ℤ := by
    rw [← h.over]
    exact mem_span_singleton_self _
  rw [under_def, mem_comap, algebraMap_int_eq, map_natCast] at h1
  exact h1

theorem card_primesOver_eq_finrank (L : Type) [Field L] [NumberField L] [Algebra E L] (N : ℕ) [NeZero N] [IsCyclotomicExtension {N} ℚ L]
    {p : ℕ} (hp : p.Prime) (hpN : p ≡ 1 [MOD N]) :
    Nat.card ((span {(p : ℤ)}).primesOver (𝓞 E)) = Module.finrank ℚ E := by
  have : Fact p.Prime := ⟨hp⟩
  have : (span {(p : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime p
  have h := sum_ramification_inertia_eq_finrank (span {(p : ℤ)}) (𝓞 E)
  rw [RingOfIntegers.rank] at h
  rw [← h, Nat.card_eq_fintype_card, Fintype.card_eq_sum_ones]
  refine Finset.sum_congr rfl fun q _ => ?_
  have := q.2.1
  have := q.2.2
  obtain ⟨h1, h2⟩ := split_of_modEq_one_cyclotomic L N hp hpN q.1
  rw [h1, h2]

theorem absNorm_eq_of_modEq_one (L : Type) [Field L] [NumberField L] [Algebra E L] (N : ℕ) [NeZero N] [IsCyclotomicExtension {N} ℚ L]
    {p : ℕ} (hp : p.Prime) (hpN : p ≡ 1 [MOD N]) (P : HeightOneSpectrum (𝓞 E)) (h : (p : 𝓞 E) ∈ P.asIdeal) :
    absNorm P.asIdeal = p := by
  have := P.isPrime
  have := liesOver_span_of_natCast_mem_columns hp P.asIdeal h
  rw [← pow_inertiaDeg p P.asIdeal, (split_of_modEq_one_cyclotomic L N hp hpN P.asIdeal).1, pow_one]

theorem card_divisors_eq_finrank (L : Type) [Field L] [NumberField L] [Algebra E L] (N : ℕ) [NeZero N] [IsCyclotomicExtension {N} ℚ L]
    {p : ℕ} (hp : p.Prime) (hpN : p ≡ 1 [MOD N]) : (divs (p : 𝓞 E)).card = Module.finrank ℚ E := by
  have hp0 : (p : 𝓞 E) ≠ 0 := by exact_mod_cast hp.ne_zero
  rw [← card_primesOver_eq_finrank L N hp hpN, ← Fintype.card_coe, ← Nat.card_eq_fintype_card]
  have hb : ∀ q : (span {(p : ℤ)}).primesOver (𝓞 E), q.1 ≠ ⊥ := by
    intro q h0
    have := q.2.2
    have h1 := natCast_mem_of_liesOver_span (p := p) q.1
    rw [h0] at h1
    exact hp0 h1
  let e : {P // P ∈ divs (p : 𝓞 E)} ≃ (span {(p : ℤ)}).primesOver (𝓞 E) :=
    { toFun := fun P => ⟨P.1.asIdeal, P.1.isPrime,
        @liesOver_span_of_natCast_mem_columns E _ _ p hp P.1.asIdeal P.1.isPrime ((mem_divs hp0 P.1).1 P.2)⟩
      invFun := fun q => ⟨⟨q.1, q.2.1, hb q⟩, (mem_divs hp0 _).2 (@natCast_mem_of_liesOver_span E _ _ p q.1 q.2.2)⟩
      left_inv := fun P => rfl
      right_inv := fun q => rfl }
  exact Nat.card_congr e

end SplitGen

theorem finiteDimensional_cyclotomic {N : ℕ} (hN : 0 < N) : FiniteDimensional ℚ (cycQ N) := fin_adjoin (finite_pow_eq N hN 1)

theorem normal_cyclotomic (N : ℕ) : Normal ℚ (cycQ N) := normal_adjoin fun s x hx => by
  show (s x) ^ N = 1
  rw [← map_pow, show x ^ N = 1 from hx, map_one]

theorem cyclotomic_mono_of_dvd {M N : ℕ} (h : M ∣ N) : cycQ M ≤ cycQ N := by
  unfold cycQ
  apply adjoin.mono
  intro z hz
  obtain ⟨c, rfl⟩ := h
  show z ^ (M * c) = 1
  rw [pow_mul, show z ^ M = 1 from hz, one_pow]

theorem cyclotomic_isCyclotomicExtension {N : ℕ} (hN : 0 < N) : IsCyclotomicExtension {N} ℚ (cycQ N) := by
  have : NeZero N := ⟨hN.ne'⟩
  have h := IntermediateField.isCyclotomicExtension_adjoin_of_exists_isPrimitiveRoot {N} ℚ Qb (by
    intro n hn _
    obtain rfl : n = N := hn
    exact HasEnoughRootsOfUnity.exists_primitiveRoot Qb n)
  have e : {b : Qb | ∃ n ∈ ({N} : Set ℕ), n ≠ 0 ∧ b ^ n = 1} = mus N := by
    ext b
    constructor
    · rintro ⟨n, hn, -, hb⟩
      obtain rfl : n = N := hn
      exact hb
    · intro hb
      exact ⟨N, rfl, hN.ne', hb⟩
  rw [e] at h
  exact h

section Split

variable {X : Fields}

theorem split_of_conductor_modEq_one {N : ℕ} (hN : 0 < N) (hc : X.IsCond N) {p : ℕ} (hp : p.Prime) (hpN : p ≡ 1 [MOD N]) :
    (∀ P : HeightOneSpectrum (𝓞 X.E), (p : 𝓞 X.E) ∈ P.asIdeal → Ideal.absNorm P.asIdeal = p) ∧
      (divs (p : 𝓞 X.E)).card = Module.finrank ℚ X.E := by
  have : NeZero N := ⟨hN.ne'⟩
  have hfd : FiniteDimensional ℚ (cycQ N) := finiteDimensional_cyclotomic hN
  have hnf : NumberField (cycQ N) := { to_charZero := inferInstance, to_finiteDimensional := hfd }
  have hcy : IsCyclotomicExtension {N} ℚ (cycQ N) := cyclotomic_isCyclotomicExtension hN
  let j : X.E →ₐ[ℚ] Qb := IsAlgClosed.lift
  have hj : ∀ x, j x ∈ cycQ N := fun x => (hc j).1 ⟨x, rfl⟩
  let f : X.E →+* cycQ N := j.toRingHom.codRestrict (cycQ N) hj
  let _ : Algebra X.E (cycQ N) := f.toAlgebra
  exact ⟨fun P h => absNorm_eq_of_modEq_one (cycQ N) N hp hpN P h, card_divisors_eq_finrank (cycQ N) N hp hpN⟩

def toyConjugatePrime (P : HeightOneSpectrum (𝓞 X.E)) : HeightOneSpectrum (𝓞 X.E) where
  asIdeal := P.asIdeal.comap X.conjO
  isPrime := Ideal.comap_isPrime _ _
  ne_bot := by
    intro h
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot
    have h1 : X.conjO x ∈ P.asIdeal.comap X.conjO := by
      rw [Ideal.mem_comap, X.conjO_invol]
      exact hx
    rw [h] at h1
    have h2 : X.conjO x = 0 := h1
    apply hx0
    rw [← X.conjO_invol x, h2, map_zero]

theorem mem_conjugatePrime_iff (P : HeightOneSpectrum (𝓞 X.E)) (x : 𝓞 X.E) : x ∈ (toyConjugatePrime P).asIdeal ↔ X.conjO x ∈ P.asIdeal := Iff.rfl

theorem conjugatePrime_involutive (P : HeightOneSpectrum (𝓞 X.E)) : toyConjugatePrime (toyConjugatePrime P) = P := by
  apply HeightOneSpectrum.ext
  ext x
  rw [mem_conjugatePrime_iff, mem_conjugatePrime_iff, X.conjO_invol]

theorem card_prime_divisors_half (hX : X.Ok) {π : 𝓞 X.E} {p : ℕ} (hp : p.Prime) (hn : π * X.conjO π = (p : 𝓞 X.E))
    (hcop : IsCoprime π (X.conjO π)) (hcard : (divs (p : 𝓞 X.E)).card = Module.finrank ℚ X.E) :
    (divs π).card = X.f := by
  classical
  have hp0 : (p : 𝓞 X.E) ≠ 0 := by exact_mod_cast hp.ne_zero
  have h1 : π ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hn
    exact hp0 hn.symm
  have h2 : X.conjO π ≠ 0 := by
    intro h
    rw [h, mul_zero] at hn
    exact hp0 hn.symm
  have hU : divs (p : 𝓞 X.E) = divs π ∪ divs (X.conjO π) := by
    ext P
    rw [Finset.mem_union, mem_divs hp0, mem_divs h1, mem_divs h2, ← hn]
    exact P.isPrime.mul_mem_iff_mem_or_mem
  have hD : Disjoint (divs π) (divs (X.conjO π)) := by
    rw [Finset.disjoint_left]
    intro P hP hP'
    rw [mem_divs h1] at hP
    rw [mem_divs h2] at hP'
    obtain ⟨a, b, hab⟩ := hcop
    apply P.isPrime.ne_top
    rw [Ideal.eq_top_iff_one, ← hab]
    exact P.asIdeal.add_mem (P.asIdeal.mul_mem_left _ hP) (P.asIdeal.mul_mem_left _ hP')
  have hB : (divs (X.conjO π)).card = (divs π).card := by
    refine Finset.card_nbij' toyConjugatePrime toyConjugatePrime ?_ ?_ (fun P _ => conjugatePrime_involutive P) (fun P _ => conjugatePrime_involutive P)
    · intro P hP
      have hP' := (mem_divs h2 P).1 hP
      exact (mem_divs h1 _).2 ((mem_conjugatePrime_iff P π).2 hP')
    · intro P hP
      have hP' := (mem_divs h1 P).1 hP
      refine (mem_divs h2 _).2 ((mem_conjugatePrime_iff P _).2 ?_)
      rw [X.conjO_invol]
      exact hP'
  rw [hU, Finset.card_union_of_disjoint hD, hB, hX.rankQ] at hcard
  omega

theorem conj_mul_conj_conj_eq {π : 𝓞 X.E} {p : ℕ} (h : π * X.conjO π = (p : 𝓞 X.E)) :
    X.conjO π * X.conjO (X.conjO π) = (p : 𝓞 X.E) := by
  rw [X.conjO_invol, mul_comm, h]

theorem isCoprime_conj_conj {π : 𝓞 X.E} (h : IsCoprime π (X.conjO π)) : IsCoprime (X.conjO π) (X.conjO (X.conjO π)) := by
  rw [X.conjO_invol]
  exact h.symm

theorem natCast_mem_of_mem_divisors {π : 𝓞 X.E} {p : ℕ} (hp : p.Prime) (hn : π * X.conjO π = (p : 𝓞 X.E))
    {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∈ divs π) : (p : 𝓞 X.E) ∈ P.asIdeal := by
  have hp0 : (p : 𝓞 X.E) ≠ 0 := by exact_mod_cast hp.ne_zero
  have h1 : π ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hn
    exact hp0 hn.symm
  rw [← hn]
  exact P.asIdeal.mul_mem_right _ ((mem_divs h1 P).1 hP)

theorem Primes.ok_of_cond (hX : X.Ok) (Pr : Primes X) (hN : 0 < Pr.cond) (hc : X.IsCond Pr.cond)
    (g_prime : ∀ i, (Pr.g i).Prime) (piG_Kq : ∀ i, ((Pr.piG i : 𝓞 X.E) : X.E) ∈ X.Kq)
    (piG_norm : ∀ i, Pr.piG i * X.conjO (Pr.piG i) = (Pr.g i : 𝓞 X.E))
    (piG_cop : ∀ i, IsCoprime (Pr.piG i) (X.conjO (Pr.piG i)))
    (g_cong : ∀ i, Pr.g i ≡ 1 [MOD Pr.cond]) (g_ne : Pr.g 0 ≠ Pr.g 1)
    (T_prime : ∀ u, (Pr.T u).Prime) (piT_Kq : ∀ u, ((Pr.piT u : 𝓞 X.E) : X.E) ∈ X.Kq)
    (piT_norm : ∀ u, Pr.piT u * X.conjO (Pr.piT u) = (Pr.T u : 𝓞 X.E))
    (piT_cop : ∀ u, IsCoprime (Pr.piT u) (X.conjO (Pr.piT u)))
    (piT_cong : ∀ u, ((Pr.cond * (Pr.g 0 * Pr.g 1) ^ 2 : ℕ) : 𝓞 X.E) ∣ Pr.piT u - 1)
    (T_cong : ∀ u, Pr.T u ≡ 1 [MOD Pr.cond]) (T_ne_g : ∀ u i, Pr.T u ≠ Pr.g i) : Pr.Ok where
  g_prime := g_prime
  piG_Kq := piG_Kq
  piG_norm := piG_norm
  piG_cop := piG_cop
  vG_card := fun i => card_prime_divisors_half hX (g_prime i) (conj_mul_conj_conj_eq (piG_norm i)) (isCoprime_conj_conj (piG_cop i))
    (split_of_conductor_modEq_one hN hc (g_prime i) (g_cong i)).2
  vG_norm := fun i w hw => (split_of_conductor_modEq_one hN hc (g_prime i) (g_cong i)).1 w
    (natCast_mem_of_mem_divisors (g_prime i) (conj_mul_conj_conj_eq (piG_norm i)) hw)
  g_cong := g_cong
  g_ne := g_ne
  T_prime := T_prime
  piT_Kq := piT_Kq
  piT_norm := piT_norm
  piT_cop := piT_cop
  vT_card := fun u => card_prime_divisors_half hX (T_prime u) (piT_norm u) (piT_cop u) (split_of_conductor_modEq_one hN hc (T_prime u) (T_cong u)).2
  vT_norm := fun u P hP => (split_of_conductor_modEq_one hN hc (T_prime u) (T_cong u)).1 P (natCast_mem_of_mem_divisors (T_prime u) (piT_norm u) hP)
  piT_cong := piT_cong
  T_ne_g := T_ne_g

end Split

section HostZ

variable {φ₁ : Formalism.HC.Frame} (H : Formalism.HC.HostRaw φ₁) (ι : Qb →+* ℂ) (LL : Fld) [FiniteDimensional ℚ LL] [Normal ℚ LL] (hE : H.EQ ≤ LL)

def hwQb (d : ℕ) : Qb := Classical.choose (exists_sqrt (-(d : ℤ)))

theorem hwQb_mem (d : ℕ) : hwQb d ∈ sqrts (-(d : ℤ)) := Classical.choose_spec (exists_sqrt (-(d : ℤ)))

theorem hwQb_sq (d : ℕ) : hwQb d ^ 2 = -(d : Qb) := by
  have h : hwQb d ^ 2 = ((-(d : ℤ) : ℤ) : Qb) := hwQb_mem d
  rw [h]; simp

theorem hwQb_mem_EQ : hwQb H.d ∈ H.EQ :=
  H.KQ_le_EQ (sqrts_sub _ (hwQb_mem H.d))

theorem conj_hwQb (hd : 0 < H.d) : conjQb ι (hwQb H.d) = -hwQb H.d := by
  have h : (conjQb ι (hwQb H.d)) ^ 2 = hwQb H.d ^ 2 := by rw [← map_pow, hwQb_sq, map_neg, map_natCast]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with h1 | h1
  · exact absurd h1 (conj_sqrt_ne ι hd (hwQb_mem H.d))
  · exact h1

def hwE : (hostFields H ι LL hE).E := (⟨hwQb H.d, hwQb_mem_EQ H⟩ : H.EQ)

theorem hwE_sq : hwE H ι LL hE ^ 2 = -(H.d : (hostFields H ι LL hE).E) := by
  have h : ((⟨hwQb H.d, hwQb_mem_EQ H⟩ : H.EQ)) ^ 2 = -(H.d : H.EQ) := Subtype.val_injective (by
    show hwQb H.d ^ 2 = _
    rw [hwQb_sq]
    simp)
  exact h

theorem star_hwE (hd : 0 < H.d) : star (hwE H ι LL hE) = -hwE H ι LL hE := by
  have h : cLL ι H.EQ (⟨hwQb H.d, hwQb_mem_EQ H⟩ : H.EQ) = -(⟨hwQb H.d, hwQb_mem_EQ H⟩ : H.EQ) :=
    Subtype.val_injective ((cLL_coe ι H.EQ _).trans (conj_hwQb H ι hd))
  exact h

theorem hwE_Kq : hwE H ι LL hE ∈ (hostFields H ι LL hE).Kq := by
  have key : ∀ g : φ₁.Psi, CoF.val ι LL ((hostFields H ι LL hE).emb g (hwE H ι LL hE)) = hwQb H.d := by
    intro g
    have h1 : CoF.val ι LL ((hostFields H ι LL hE).emb g (hwE H ι LL hE)) =
        embQ H (g : φ₁.GG) (⟨hwQb H.d, hwQb_mem_EQ H⟩ : H.EQ) := tauLL_coe hE _ _
    rw [h1]
    by_cases h : ∃ s : H.EQ →ₐ[ℚ] Qb, H.ActsAs s (g : φ₁.GG)
    · have e1 : embQ H (g : φ₁.GG) = h.choose := dif_pos h
      have h2 := h.choose_spec.sqrt_d (⟨hwQb H.d, hwQb_mem_EQ H⟩ : H.EQ) (hwQb_mem H.d)
      rw [e1, h2, (Formalism.HC.Frame.mem_Psi_iff _).1 g.2]
      simp
    · have e1 : embQ H (g : φ₁.GG) = H.EQ.val := dif_neg h
      rw [e1]
      rfl
  intro (g : φ₁.Psi) (g' : φ₁.Psi)
  apply CoF.val_injective ι LL
  rw [key g, key g']

def hwO : 𝓞 (hostFields H ι LL hE).E :=
  ⟨hwE H ι LL hE, IsIntegral.of_pow (n := 2) (by norm_num) (by rw [hwE_sq]; exact (isIntegral_natCast H.d).neg)⟩

theorem hwO_sq : hwO H ι LL hE ^ 2 = -(H.d : 𝓞 (hostFields H ι LL hE).E) :=
  RingOfIntegers.ext (by
    rw [RingOfIntegers.coe_eq_algebraMap, RingOfIntegers.coe_eq_algebraMap, map_pow, map_neg, map_natCast]
    exact hwE_sq H ι LL hE)

theorem conjO_hwO (hd : 0 < H.d) : (hostFields H ι LL hE).conjO (hwO H ι LL hE) = -hwO H ι LL hE :=
  RingOfIntegers.ext (star_hwE H ι LL hE hd)

def hz (a b : ℤ) : 𝓞 (hostFields H ι LL hE).E :=
  (a : 𝓞 (hostFields H ι LL hE).E) + (b : 𝓞 (hostFields H ι LL hE).E) * hwO H ι LL hE

theorem conjO_hz (hd : 0 < H.d) (a b : ℤ) : (hostFields H ι LL hE).conjO (hz H ι LL hE a b) = hz H ι LL hE a (-b) := by
  unfold hz
  rw [map_add, map_mul, map_intCast, map_intCast, conjO_hwO H ι LL hE hd]
  push_cast
  ring

theorem hz_norm (hd : 0 < H.d) (a b : ℤ) (p : ℕ) (h : a ^ 2 + H.d * b ^ 2 = p) :
    hz H ι LL hE a b * (hostFields H ι LL hE).conjO (hz H ι LL hE a b) = (p : 𝓞 (hostFields H ι LL hE).E) := by
  have hc : ((a ^ 2 + H.d * b ^ 2 : ℤ) : 𝓞 (hostFields H ι LL hE).E) = (p : 𝓞 (hostFields H ι LL hE).E) := by
    rw [h]; simp
  push_cast at hc
  rw [conjO_hz H ι LL hE hd]
  unfold hz
  push_cast
  linear_combination (-(b : 𝓞 (hostFields H ι LL hE).E) ^ 2) * hwO_sq H ι LL hE + hc

theorem hz_cop (hd : 0 < H.d) (a b x y : ℤ) (h : x * (2 * a) + y * (a ^ 2 + H.d * b ^ 2) = 1) :
    IsCoprime (hz H ι LL hE a b) ((hostFields H ι LL hE).conjO (hz H ι LL hE a b)) := by
  have hc : ((x * (2 * a) + y * (a ^ 2 + H.d * b ^ 2) : ℤ) : 𝓞 (hostFields H ι LL hE).E) = 1 := by
    rw [h]; simp
  push_cast at hc
  refine ⟨(x : 𝓞 (hostFields H ι LL hE).E) + (y : 𝓞 (hostFields H ι LL hE).E) * hz H ι LL hE a (-b),
    (x : 𝓞 (hostFields H ι LL hE).E), ?_⟩
  rw [conjO_hz H ι LL hE hd]
  unfold hz
  push_cast
  linear_combination (-(y : 𝓞 (hostFields H ι LL hE).E) * (b : 𝓞 (hostFields H ι LL hE).E) ^ 2) * hwO_sq H ι LL hE + hc

theorem hz_Kq (a b : ℤ) : ((hz H ι LL hE a b : 𝓞 (hostFields H ι LL hE).E) : (hostFields H ι LL hE).E) ∈
    (hostFields H ι LL hE).Kq := by
  have h : ((hz H ι LL hE a b : 𝓞 (hostFields H ι LL hE).E) : (hostFields H ι LL hE).E) =
      (a : (hostFields H ι LL hE).E) + (b : (hostFields H ι LL hE).E) * hwE H ι LL hE := by
    rw [RingOfIntegers.coe_eq_algebraMap]
    unfold hz
    rw [map_add, map_mul, map_intCast, map_intCast]
    rfl
  rw [h]
  exact add_mem (intCast_mem _ a) (mul_mem (intCast_mem _ b) (hwE_Kq H ι LL hE))

theorem hz_cong (n : ℕ) (c : ℤ) : ((n : ℕ) : 𝓞 (hostFields H ι LL hE).E) ∣ hz H ι LL hE 1 (n * c) - 1 := by
  refine ⟨hz H ι LL hE 0 c, ?_⟩
  unfold hz
  push_cast
  ring

end HostZ

theorem lucas_primality_test (p a f : ℕ) (L : List (ℕ × ℕ)) (hp1 : 1 < p) (hL : ∀ x ∈ L, x.1.Prime)
    (hprod : (L.map fun x => x.1 ^ x.2).prod = p - 1) (hf : p - 1 < 2 ^ f) (h1 : ndPowMod p f a (p - 1) = 1)
    (h2 : ∀ x ∈ L, ndPowMod p f a ((p - 1) / x.1) % p ≠ 1) : p.Prime := by
  refine lucas_primality p ((a : ℕ) : ZMod p) ?_ ?_
  · rw [ndPowMod_zmod p f a (p - 1) 1 hf h1, Nat.cast_one]
  · intro q hq hd
    rw [← hprod] at hd
    obtain ⟨y, hy, hqy⟩ := (Prime.dvd_prod_iff hq.prime).1 hd
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
    have hqx : q = x.1 := (Nat.prime_dvd_prime_iff_eq hq (hL x hx)).1 (hq.dvd_of_dvd_pow hqy)
    subst hqx
    rw [ndPowMod_zmod p f a ((p - 1) / x.1) _ (lt_of_le_of_lt (Nat.div_le_self _ _) hf) rfl]
    intro h
    have h3 : ((ndPowMod p f a ((p - 1) / x.1) : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by rw [h, Nat.cast_one]
    have h4 := (ZMod.natCast_eq_natCast_iff' _ _ _).1 h3
    rw [Nat.mod_eq_of_lt hp1] at h4
    exact h2 x hx h4

def toyFirstParameter : ℕ := 5812161310401002497

def toySecondParameter : ℕ := 10580716767734447210497

def nd2T : ℕ := 56194698826333161291662198507648755438473557111144279252246328293211974734191775333427954228508737780869538570051953955243454133837703637171933755744705457828859522702609327843686445057

def columnDegreeBound : ℕ := 175899382716746995995794692370095808443505986460327359316203003947391329197558870718244898147225575657278023097973275990081581282841096000378419862656504066221696375796925055794734493697

theorem example_first_prime : toyFirstParameter.Prime := by
  refine lucas_primality_test toyFirstParameter 5 63 [(2, 10), (3, 4), (571, 2), (599, 3)] (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;> norm_num

theorem example_second_prime : toySecondParameter.Prime := by
  refine lucas_primality_test toySecondParameter 5 74 [(2, 24), (3, 2), (571, 2), (599, 3)] (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;> norm_num

theorem nd2T_prime : nd2T.Prime := by
  refine lucas_primality_test nd2T 5 614 [(2, 12), (3, 4), (13, 2), (571, 2), (599, 3), (toyFirstParameter, 4), (toySecondParameter, 4)] (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact example_first_prime
  · exact example_second_prime

theorem columns_prime_fact : columnDegreeBound.Prime := by
  refine lucas_primality_test columnDegreeBound 5 616 [(2, 12), (3, 4), (23, 2), (571, 2), (599, 3), (toyFirstParameter, 4), (toySecondParameter, 4)] (by decide +kernel) ?_
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact example_first_prime
  · exact example_second_prime

section CharsGen

variable {X : Fields}

theorem two_sq_ne_two_pow_four {p : ℕ} (h : 16 < p) : (2 : ZMod p) ^ 2 ≠ 2 ^ 4 := by
  intro h1
  have h2 : ((4 : ℕ) : ZMod p) = ((16 : ℕ) : ZMod p) := by
    push_cast
    norm_num at h1 ⊢
    exact h1
  have h3 := (ZMod.natCast_eq_natCast_iff' _ _ _).1 h2
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt h] at h3
  omega

theorem characters_at_prime_exist (w : HeightOneSpectrum (𝓞 X.E)) {p : ℕ} (hp : p.Prime) (hw : Ideal.absNorm w.asIdeal = p) (h16 : 16 < p)
    (Ψ : ∀ q : ℕ, AddChar (ZMod q) X.K) (hΨ : Ψ p ≠ 1) (om : ∀ q : ℕ, (ZMod q)ˣ →* X.Kˣ) (hom : Function.Injective (om p)) :
    ∃ (ψ : AddChar (𝓞 X.E ⧸ w.asIdeal) X.K) (χ : Fin 2 → ((𝓞 X.E ⧸ w.asIdeal)ˣ →* X.Kˣ)), ψ ≠ 1 ∧ Function.Injective χ ∧
      ∀ q : ℕ, Ideal.absNorm w.asIdeal = q → (∀ a : ℤ, ψ (a : 𝓞 X.E ⧸ w.asIdeal) = Ψ q (a : ZMod q)) ∧
        ∃ θ : (𝓞 X.E ⧸ w.asIdeal)ˣ →* (ZMod q)ˣ,
          (∀ (x : (𝓞 X.E ⧸ w.asIdeal)ˣ) (a : ℤ), (x : 𝓞 X.E ⧸ w.asIdeal) = (a : 𝓞 X.E ⧸ w.asIdeal) →
            ((θ x : (ZMod q)ˣ) : ZMod q) = (a : ZMod q)) ∧
          ∀ (j : Fin 2) (x : (𝓞 X.E ⧸ w.asIdeal)ˣ), χ j x = om q (θ x) ^ (2 * (j.1 + 1)) := by
  have hfin : Finite (𝓞 X.E ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot w.asIdeal w.ne_bot
  have hcard : Nat.card (𝓞 X.E ⧸ w.asIdeal) = p := by
    rw [← hw, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have : Fintype (𝓞 X.E ⧸ w.asIdeal) := Fintype.ofFinite _
  let e : ZMod p ≃+* (𝓞 X.E ⧸ w.asIdeal) := ZMod.ringEquivOfPrime _ hp (by rw [← Nat.card_eq_fintype_card, hcard])
  let θ : (𝓞 X.E ⧸ w.asIdeal)ˣ →* (ZMod p)ˣ := Units.map e.symm.toRingHom.toMonoidHom
  have hθs : Function.Surjective θ := fun a => ⟨Units.map e.toRingHom.toMonoidHom a, Units.ext (e.symm_apply_apply _)⟩
  have hθ : ∀ (x : (𝓞 X.E ⧸ w.asIdeal)ˣ) (a : ℤ), (x : 𝓞 X.E ⧸ w.asIdeal) = (a : 𝓞 X.E ⧸ w.asIdeal) →
      ((θ x : (ZMod p)ˣ) : ZMod p) = (a : ZMod p) := by
    intro x a hx
    show e.symm (x : 𝓞 X.E ⧸ w.asIdeal) = (a : ZMod p)
    rw [hx, map_intCast]
  have h2 : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).2 (by omega)
  have key : ∀ n n' : ℕ, ((om p).comp θ) ^ n = ((om p).comp θ) ^ n' → (2 : ZMod p) ^ n = 2 ^ n' := by
    intro n n' h
    obtain ⟨x, hx⟩ := hθs (ZMod.unitOfCoprime 2 h2)
    have h1 := DFunLike.congr_fun h x
    rw [MonoidHom.pow_apply, MonoidHom.pow_apply, MonoidHom.comp_apply, hx, ← map_pow, ← map_pow] at h1
    have h3 := congrArg Units.val (hom h1)
    rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime] at h3
    exact_mod_cast h3
  have h24 := two_sq_ne_two_pow_four h16
  refine ⟨(Ψ p).compAddMonoidHom e.symm.toAddEquiv.toAddMonoidHom, fun j => ((om p).comp θ) ^ (2 * (j.1 + 1)), ?_, ?_, ?_⟩
  · intro h
    apply hΨ
    ext y
    have h1 := DFunLike.congr_fun h (e y)
    rw [AddChar.compAddMonoidHom_apply] at h1
    have h3 : e.symm.toAddEquiv.toAddMonoidHom (e y) = y := e.symm_apply_apply y
    rw [h3] at h1
    exact h1
  · intro j j' h
    fin_cases j <;> fin_cases j'
    · rfl
    · exact (h24 (key 2 4 h)).elim
    · exact (h24 (key 4 2 h).symm).elim
    · rfl
  · intro q hq
    obtain rfl : p = q := hw.symm.trans hq
    refine ⟨fun a => ?_, θ, hθ, fun j x => ?_⟩
    · rw [AddChar.compAddMonoidHom_apply]
      have h3 : e.symm.toAddEquiv.toAddMonoidHom ((a : ℤ) : 𝓞 X.E ⧸ w.asIdeal) = (a : ZMod p) := map_intCast e.symm a
      rw [h3]
    · rw [MonoidHom.pow_apply, MonoidHom.comp_apply]

theorem exists_nontrivial_additiveChar (M : Type) [Field M] {p : ℕ} (hp : p.Prime) [HasEnoughRootsOfUnity M p] :
    ∃ ψ : AddChar (ZMod p) M, ψ ≠ 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have hex : Monoid.exponent (Multiplicative (ZMod p)) ∣ p := by
    have h := Group.exponent_dvd_nat_card (G := Multiplicative (ZMod p))
    rwa [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card] at h
  have := HasEnoughRootsOfUnity.of_dvd M hex
  exact exists_addChar_ne

theorem exists_injective_unit_character (M : Type) [Field M] {p : ℕ} (hp : p.Prime) [HasEnoughRootsOfUnity M (p - 1)] :
    ∃ φ : (ZMod p)ˣ →* Mˣ, Function.Injective φ := by
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero (p - 1) := ⟨by have := hp.one_lt; omega⟩
  have hex : Monoid.exponent (ZMod p)ˣ ∣ p - 1 := by
    rw [← ZMod.card_units p]
    exact Group.exponent_dvd_card
  have := HasEnoughRootsOfUnity.of_dvd M hex
  exact exists_faithful _ _

variable {Pr : Primes X}

theorem characters_exist_of_roots (hPr : Pr.Ok) (h1 : ∀ i, HasEnoughRootsOfUnity X.K (Pr.g i)) (h2 : ∀ i, HasEnoughRootsOfUnity X.K (Pr.g i - 1))
    (h16 : ∀ i, 16 < Pr.g i) : ∃ Ch : Chars X Pr 2, Ch.Ok := by
  classical
  have hi : ∀ w : {w // w ∈ Pr.vGs}, ∃ i, w.1 ∈ Pr.vG i := by
    intro w
    have hw := w.2
    unfold Primes.vGs at hw
    rcases Finset.mem_union.1 hw with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  have hfΨ : ∀ i, ∃ ψ : AddChar (ZMod (Pr.g i)) X.K, ψ ≠ 1 := fun i => by
    have := h1 i
    exact exists_nontrivial_additiveChar X.K (hPr.g_prime i)
  have hfo : ∀ i, ∃ φ : (ZMod (Pr.g i))ˣ →* X.Kˣ, Function.Injective φ := fun i => by
    have := h2 i
    exact exists_injective_unit_character X.K (hPr.g_prime i)
  let Ψ : ∀ q : ℕ, AddChar (ZMod q) X.K := fun q => if h : ∃ ψ : AddChar (ZMod q) X.K, ψ ≠ 1 then h.choose else 1
  let om : ∀ q : ℕ, (ZMod q)ˣ →* X.Kˣ := fun q =>
    if h : ∃ φ : (ZMod q)ˣ →* X.Kˣ, Function.Injective φ then h.choose else 1
  have hΨ : ∀ i, Ψ (Pr.g i) ≠ 1 := by
    intro i
    have e : Ψ (Pr.g i) = (hfΨ i).choose := dif_pos (hfΨ i)
    rw [e]
    exact (hfΨ i).choose_spec
  have hom : ∀ i, Function.Injective (om (Pr.g i)) := by
    intro i
    have e : om (Pr.g i) = (hfo i).choose := dif_pos (hfo i)
    rw [e]
    exact (hfo i).choose_spec
  have key := fun w : {w // w ∈ Pr.vGs} =>
    characters_at_prime_exist w.1 (hPr.g_prime (hi w).choose) (hPr.vG_norm _ w.1 (hi w).choose_spec) (h16 _) Ψ (hΨ _) om (hom _)
  choose ψ χ hψ hχ hq using key
  refine ⟨{ psi0 := ψ, chi := fun j w => χ w j, muVal := fun _ _ => 1, etaVal := fun _ => 1 }, hψ, hχ, ?_, ?_, ?_⟩
  · intro i w w' hw hw' j a x x' hx hx'
    obtain ⟨-, θ, hθ, hc⟩ := hq w _ (hPr.vG_norm i w.1 hw)
    obtain ⟨-, θ', hθ', hc'⟩ := hq w' _ (hPr.vG_norm i w'.1 hw')
    show χ w j x = χ w' j x'
    rw [hc, hc', show θ x = θ' x' from Units.ext ((hθ x a hx).trans (hθ' x' a hx').symm)]
  · intro i w w' hw hw' a
    show ψ w _ = ψ w' _
    rw [(hq w _ (hPr.vG_norm i w.1 hw)).1 a, (hq w' _ (hPr.vG_norm i w'.1 hw')).1 a]
  · intro i
    have : NeZero (Pr.g i) := ⟨(hPr.g_prime i).ne_zero⟩
    refine ⟨om _, hom i, fun w hw j a x hx => ?_⟩
    obtain ⟨-, θ, hθ, hc⟩ := hq w _ (hPr.vG_norm i w.1 hw)
    show χ w j x = _
    rw [hc]
    have h3 : θ x = a := by
      apply Units.ext
      rw [hθ x (((a : ZMod (Pr.g i)).val : ℕ) : ℤ) (by rw [hx, Int.cast_natCast]), Int.cast_natCast, ZMod.natCast_zmod_val]
    rw [h3]

theorem additiveChars_at_T_exist (hPr : Pr.Ok) (h1 : ∀ u, HasEnoughRootsOfUnity X.K (Pr.T u)) : ∃ Ps : CharT X Pr, Ps.Ok := by
  classical
  have key : ∀ (u : Pr.Word), ∃ Ψ : AddChar (ZMod (Pr.T u)) X.K, Ψ ≠ 1 := fun u => by
    have := h1 u
    exact exists_nontrivial_additiveChar X.K (hPr.T_prime u)
  choose Ψ hΨ using key
  have key2 : ∀ (u : Pr.Word) (P : {P // P ∈ Pr.vT u}), ∃ ψ : AddChar (𝓞 X.E ⧸ P.1.asIdeal) X.K, ψ ≠ 1 ∧
      ∀ a : ℤ, ψ (a : 𝓞 X.E ⧸ P.1.asIdeal) = Ψ u (a : ZMod (Pr.T u)) := by
    intro u P
    have hfin : Finite (𝓞 X.E ⧸ P.1.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot P.1.asIdeal P.1.ne_bot
    have hcard : Nat.card (𝓞 X.E ⧸ P.1.asIdeal) = Pr.T u := by
      rw [← hPr.vT_norm u P.1 P.2, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    have : Fintype (𝓞 X.E ⧸ P.1.asIdeal) := Fintype.ofFinite _
    let e : ZMod (Pr.T u) ≃+* (𝓞 X.E ⧸ P.1.asIdeal) :=
      ZMod.ringEquivOfPrime _ (hPr.T_prime u) (by rw [← Nat.card_eq_fintype_card, hcard])
    refine ⟨(Ψ u).compAddMonoidHom e.symm.toAddEquiv.toAddMonoidHom, ?_, fun a => ?_⟩
    · intro h
      apply hΨ u
      ext y
      have h1 := DFunLike.congr_fun h (e y)
      rw [AddChar.compAddMonoidHom_apply] at h1
      have h3 : e.symm.toAddEquiv.toAddMonoidHom (e y) = y := e.symm_apply_apply y
      rw [h3] at h1
      exact h1
    · rw [AddChar.compAddMonoidHom_apply]
      have h3 : e.symm.toAddEquiv.toAddMonoidHom ((a : ℤ) : 𝓞 X.E ⧸ P.1.asIdeal) = (a : ZMod (Pr.T u)) := map_intCast e.symm a
      rw [h3]
  choose ψ hψ hs using key2
  exact ⟨⟨ψ⟩, hψ, fun u P P' a => (hs u P a).trans (hs u P' a).symm⟩

end CharsGen

section Hecke

variable {X : Fields} {Pr : Primes X} {R : Ranks}

def Chars.HeckeEx (Ch : Chars X Pr R.m) (W : Wts X Pr.Word R) (σ₀ : X.K →+* ℂ) : Prop :=
  ∃ (mu : Fin R.m → HChar X.E) (eta : HChar X.E), (∀ j, IsMu0 Ch σ₀ (fun τ => (W.row τ).e j) j (mu j)) ∧
    (∀ j, (mu j).ValuesIn 0 σ₀) ∧ IsEtaT X σ₀ eta ∧ eta.ValuesIn (1 / 2) σ₀

open Classical in

def Chars.ofHecke (Ch : Chars X Pr R.m) (σ₀ : X.K →+* ℂ) (mu : Fin R.m → HChar X.E) (eta : HChar X.E) : Chars X Pr R.m where
  psi0 := Ch.psi0
  chi := Ch.chi
  muVal := fun j v => if h : ∃ y : X.Kˣ, σ₀ (y : X.K) = (((mu j).val v : ℂˣ) : ℂ) then h.choose else 1
  etaVal := fun v => if h : ∃ y : X.Kˣ, σ₀ (y : X.K) = eta.valTw (1 / 2) v then h.choose else 1

theorem Chars.ofHecke_ok {Ch : Chars X Pr R.m} (h : Ch.Ok) (σ₀ : X.K →+* ℂ) (mu : Fin R.m → HChar X.E) (eta : HChar X.E) :
    (Ch.ofHecke σ₀ mu eta).Ok :=
  ⟨h.psi_zero_nontrivial_character, h.chi_inj, h.chi_same, h.characterAgreesOnPlaces, h.chi_om⟩

theorem exists_unit_of_image {σ₀ : X.K →+* ℂ} {z : ℂ} (hz : z ≠ 0) (h : ∃ y : X.K, σ₀ y = z) : ∃ y : X.Kˣ, σ₀ (y : X.K) = z := by
  obtain ⟨y, hy⟩ := h
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [map_zero] at hy
    exact hz hy.symm
  exact ⟨Units.mk0 y hy0, hy⟩

theorem twistedValue_ne_zero (χ : HChar X.E) (s : ℝ) (v : HeightOneSpectrum (𝓞 X.E)) : χ.valTw s v ≠ 0 := by
  unfold HChar.valTw
  refine mul_ne_zero (Units.ne_zero _) ?_
  have h1 : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ≠ 0 := by
    have : Ideal.absNorm v.asIdeal ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]
      exact v.ne_bot
    exact_mod_cast this
  rw [Complex.cpow_def_of_ne_zero h1]
  exact Complex.exp_ne_zero _

theorem twistedValue_zero (χ : HChar X.E) (v : HeightOneSpectrum (𝓞 X.E)) : χ.valTw 0 v = ((χ.val v : ℂˣ) : ℂ) := by
  unfold HChar.valTw
  simp

theorem Chars.ofHecke_tied {Ch : Chars X Pr R.m} {W : Wts X Pr.Word R} {σ₀ : X.K →+* ℂ} {mu : Fin R.m → HChar X.E} {eta : HChar X.E}
    (h1 : ∀ j, IsMu0 Ch σ₀ (fun τ => (W.row τ).e j) j (mu j)) (h2 : ∀ j, (mu j).ValuesIn 0 σ₀) (h3 : IsEtaT X σ₀ eta)
    (h4 : eta.ValuesIn (1 / 2) σ₀) : (Ch.ofHecke σ₀ mu eta).Tied σ₀ (fun j τ => (W.row τ).e j) mu eta where
  mu0 := fun j => ⟨(h1 j).unitary, (h1 j).triv, (h1 j).inf, (h1 j).unr, (h1 j).tame, (h1 j).atg⟩
  muVal := fun j v hv => by
    have hex : ∃ y : X.Kˣ, σ₀ (y : X.K) = (((mu j).val v : ℂˣ) : ℂ) := by
      refine exists_unit_of_image (Units.ne_zero _) ?_
      rw [← twistedValue_zero]
      exact h2 j v ((h1 j).unr v hv)
    have e : (Ch.ofHecke σ₀ mu eta).muVal j v = hex.choose := dif_pos hex
    rw [e]
    exact hex.choose_spec
  etaT := h3
  etaVal := fun v => by
    have hex : ∃ y : X.Kˣ, σ₀ (y : X.K) = eta.valTw (1 / 2) v :=
      exists_unit_of_image (twistedValue_ne_zero eta _ v) (h4 v (h3.unr v))
    have e : (Ch.ofHecke σ₀ mu eta).etaVal v = hex.choose := dif_pos hex
    rw [e]
    exact hex.choose_spec

end Hecke

def nd2N : ℕ := 204572886511813553061037407562329625995783655411690436542768105489192394035355663504895707466548678171695054788500010062488923813826764064938234928730947196464262768270018653110228498338042697795156970159903677022807129186961004810571117527615229822789011462114279289419559348825463524785325415815445950503458435921145728668675289394505621558664460319354973532563002004291054537384997546176343222140701606270894674242774158138205418672187221164903157007908864

theorem example_level_pos : 0 < nd2N := by decide +kernel

theorem exampleField_le_cyclotomic : Examples₂.H0.EQ ≤ cycQ nd2N :=
  (condEQ Examples₂.H0).1.trans (cyclotomic_mono_of_dvd (by decide +kernel))

theorem example_discriminant_pos : 0 < Examples₂.H0.d := by decide

theorem example_conductor_pos : 0 < Examples₂.H0.condN := by decide +kernel

theorem example_first_prime_norm_form : (1 : ℤ) ^ 2 + (Examples₂.H0.d : ℤ) * (((Examples₂.H0.condN : ℕ) : ℤ) * 18) ^ 2 = (toyFirstParameter : ℤ) := by
  decide +kernel

theorem example_second_prime_norm_form : (1 : ℤ) ^ 2 + (Examples₂.H0.d : ℤ) * (((Examples₂.H0.condN : ℕ) : ℤ) * 768) ^ 2 = (toySecondParameter : ℤ) := by
  decide +kernel

theorem num_nT : (1 : ℤ) ^ 2 + (Examples₂.H0.d : ℤ) *
    (((Examples₂.H0.condN * (toyFirstParameter * toySecondParameter) ^ 2 : ℕ) : ℤ) * 468) ^ 2 = (nd2T : ℤ) := by
  decide +kernel

theorem one_sq_add_d_mul_sq_eq_nd2T1 : (1 : ℤ) ^ 2 + (Examples₂.H0.d : ℤ) *
    (((Examples₂.H0.condN * (toyFirstParameter * toySecondParameter) ^ 2 : ℕ) : ℤ) * 828) ^ 2 = (columnDegreeBound : ℤ) := by
  decide +kernel

theorem columns_num_fact : -(((columnDegreeBound - 1) / 2 : ℕ) : ℤ) * (2 * 1) + 1 * ((1 : ℤ) ^ 2 + (Examples₂.H0.d : ℤ) *
    (((Examples₂.H0.condN * (toyFirstParameter * toySecondParameter) ^ 2 : ℕ) : ℤ) * 828) ^ 2) = 1 := by
  decide +kernel

theorem columns_num_fact_bis : columnDegreeBound ≡ 1 [MOD Examples₂.H0.condN] := by decide +kernel

theorem columns_num_fact_ter : columnDegreeBound ≠ toyFirstParameter ∧ columnDegreeBound ≠ toySecondParameter ∧ nd2T ≠ columnDegreeBound := by decide +kernel

theorem example_first_prime_identity : -(((toyFirstParameter - 1) / 2 : ℕ) : ℤ) * (2 * 1) +
    1 * ((1 : ℤ) ^ 2 + (Examples₂.H0.d : ℤ) * (((Examples₂.H0.condN : ℕ) : ℤ) * 18) ^ 2) = 1 := by
  decide +kernel

theorem example_second_prime_identity : -(((toySecondParameter - 1) / 2 : ℕ) : ℤ) * (2 * 1) +
    1 * ((1 : ℤ) ^ 2 + (Examples₂.H0.d : ℤ) * (((Examples₂.H0.condN : ℕ) : ℤ) * 768) ^ 2) = 1 := by
  decide +kernel

theorem num_cT : -(((nd2T - 1) / 2 : ℕ) : ℤ) * (2 * 1) + 1 * ((1 : ℤ) ^ 2 + (Examples₂.H0.d : ℤ) *
    (((Examples₂.H0.condN * (toyFirstParameter * toySecondParameter) ^ 2 : ℕ) : ℤ) * 468) ^ 2) = 1 := by
  decide +kernel

theorem example_first_prime_modEq_one : toyFirstParameter ≡ 1 [MOD Examples₂.H0.condN] := by decide +kernel

theorem example_second_prime_modEq_one : toySecondParameter ≡ 1 [MOD Examples₂.H0.condN] := by decide +kernel

theorem num_mT : nd2T ≡ 1 [MOD Examples₂.H0.condN] := by decide +kernel

theorem example_primes_distinct : toyFirstParameter ≠ toySecondParameter ∧ nd2T ≠ toyFirstParameter ∧ nd2T ≠ toySecondParameter := by decide +kernel

section Inst

variable (LL : Fld) [FiniteDimensional ℚ LL] [Normal ℚ LL] (hLL : cycQ nd2N ≤ LL)

abbrev nd2X : Fields := hostFields Examples₂.H0.toHostRaw ndIota LL (exampleField_le_cyclotomic.trans hLL)

abbrev nd2z (a b : ℤ) : 𝓞 (nd2X LL hLL).E := hz Examples₂.H0.toHostRaw ndIota LL (exampleField_le_cyclotomic.trans hLL) a b

def toyPrimes : Primes (nd2X LL hLL) where
  cond := Examples₂.H0.condN
  g := ![toyFirstParameter, toySecondParameter]
  piG := ![nd2z LL hLL 1 (((Examples₂.H0.condN : ℕ) : ℤ) * 18),
    nd2z LL hLL 1 (((Examples₂.H0.condN : ℕ) : ℤ) * 768)]
  Word := Fin 2
  T := ![nd2T, columnDegreeBound]
  piT := ![nd2z LL hLL 1 (((Examples₂.H0.condN * (toyFirstParameter * toySecondParameter) ^ 2 : ℕ) : ℤ) * 468),
    nd2z LL hLL 1 (((Examples₂.H0.condN * (toyFirstParameter * toySecondParameter) ^ 2 : ℕ) : ℤ) * 828)]

theorem exampleFields_ok : (nd2X LL hLL).Ok := hostFields_ok Examples₂.H0 ndIota LL _

theorem exampleFields_degree : (nd2X LL hLL).f = Examples₂.R0.f := hostFields_f Examples₂.H0 ndIota LL _

theorem exampleFields_conductor : (nd2X LL hLL).IsCond (toyPrimes LL hLL).cond := hostFields_isCond Examples₂.H0 ndIota LL _

theorem examplePrimes_ok : (toyPrimes LL hLL).Ok := by
  refine Primes.ok_of_cond (exampleFields_ok LL hLL) (toyPrimes LL hLL) example_conductor_pos (exampleFields_conductor LL hLL)
    (Fin.forall_fin_two.2 ⟨example_first_prime, example_second_prime⟩) (Fin.forall_fin_two.2 ⟨hz_Kq _ _ _ _ _ _, hz_Kq _ _ _ _ _ _⟩)
    (Fin.forall_fin_two.2 ⟨hz_norm _ _ _ _ example_discriminant_pos _ _ _ example_first_prime_norm_form, hz_norm _ _ _ _ example_discriminant_pos _ _ _ example_second_prime_norm_form⟩)
    (Fin.forall_fin_two.2 ⟨hz_cop _ _ _ _ example_discriminant_pos _ _ _ _ example_first_prime_identity, hz_cop _ _ _ _ example_discriminant_pos _ _ _ _ example_second_prime_identity⟩)
    (Fin.forall_fin_two.2 ⟨example_first_prime_modEq_one, example_second_prime_modEq_one⟩) example_primes_distinct.1
    (Fin.forall_fin_two.2 ⟨nd2T_prime, columns_prime_fact⟩) (Fin.forall_fin_two.2 ⟨hz_Kq _ _ _ _ _ _, hz_Kq _ _ _ _ _ _⟩)
    (Fin.forall_fin_two.2 ⟨hz_norm _ _ _ _ example_discriminant_pos _ _ _ num_nT, hz_norm _ _ _ _ example_discriminant_pos _ _ _ one_sq_add_d_mul_sq_eq_nd2T1⟩)
    (Fin.forall_fin_two.2 ⟨hz_cop _ _ _ _ example_discriminant_pos _ _ _ _ num_cT, hz_cop _ _ _ _ example_discriminant_pos _ _ _ _ columns_num_fact⟩)
    (Fin.forall_fin_two.2 ⟨hz_cong _ _ _ _ _ _, hz_cong _ _ _ _ _ _⟩) (Fin.forall_fin_two.2 ⟨num_mT, columns_num_fact_bis⟩)
    (Fin.forall_fin_two.2 ⟨Fin.forall_fin_two.2 ⟨example_primes_distinct.2.1, example_primes_distinct.2.2⟩,
      Fin.forall_fin_two.2 ⟨columns_num_fact_ter.1, columns_num_fact_ter.2.1⟩⟩)

end Inst

section Gen

open ComplexOrder

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

end Gen

theorem example_primes_gt_sixteen : 16 < toyFirstParameter ∧ 16 < toySecondParameter := by decide +kernel

theorem example_primes_dvd_level : toyFirstParameter ∣ nd2N ∧ toySecondParameter ∣ nd2N ∧ toyFirstParameter - 1 ∣ nd2N ∧ toySecondParameter - 1 ∣ nd2N ∧ nd2T ∣ nd2N ∧ columnDegreeBound ∣ nd2N := by
  decide +kernel

def nd2Z (top lt : Bool) : Fin 8 → ℤ := ![if top then 170 else 56, if lt then 22 else 23, 19, 15, 11, 7, 3, -1]

def toyHarishChandraParameter (top lt : Bool) : HCParam Examples₂.R0 where
  u := fun i => (nd2Z top lt i : ℚ) + 1 / 2
  v := Examples₂.hcV
  b := Examples₂.hcB
  e := Examples₂.hcE
  u_gt_v := by
    intro i
    cases top <;> cases lt <;> fin_cases i <;> simp [nd2Z, Examples₂.hcV] <;> norm_num
  v_gt_u := by
    intro i
    cases top <;> cases lt <;> fin_cases i <;> simp [nd2Z, Examples₂.hcV] <;> norm_num
  u_last_gt := by
    intro h h'
    simp [nd2Z, Examples₂.hcB, Examples₂.R0]
    norm_num
  gap_be := Examples₂.hc0.gap_be
  gap_eb := Examples₂.hc0.gap_eb
  e_int := Examples₂.hc0.e_int
  u_half := fun i => ⟨nd2Z top lt i, rfl⟩
  v_int := Examples₂.hc0.v_int
  b_int := Examples₂.hc0.b_int

def toyTopRoots : Finset (Examples₂.R0.Psi) := hostTops Examples₂.R0.toFrame {0}

open Classical in

def toyIsTopRoot (τ : Examples₂.R0.Psi) : Bool := decide (τ ∈ toyTopRoots)

def toyLetterSign : Fin 2 → Bool := ![false, true]

section Inst

variable (LL : Fld) [FiniteDimensional ℚ LL] [Normal ℚ LL] (hLL : cycQ nd2N ≤ LL)

def nd2W : Wts (nd2X LL hLL) (toyPrimes LL hLL).Word Examples₂.R0 where
  row := fun _ => RowPar.of Examples₂.hc0
  hc := fun (u : Fin 2) (τ : Examples₂.R0.Psi) => toyHarishChandraParameter (toyIsTopRoot τ) (toyLetterSign u)
  tops := toyTopRoots

include hLL in
theorem example_enough_roots {n : ℕ} (hn : n ∣ nd2N) : HasEnoughRootsOfUnity (CoF ndIota LL) n := hasEnoughRoots ndIota LL example_level_pos hn hLL

theorem exampleCharacters_exist : ∃ Ch : Chars (nd2X LL hLL) (toyPrimes LL hLL) Examples₂.R0.m, Ch.Ok :=
  characters_exist_of_roots (examplePrimes_ok LL hLL)
    (Fin.forall_fin_two.2 ⟨example_enough_roots LL hLL example_primes_dvd_level.1, example_enough_roots LL hLL example_primes_dvd_level.2.1⟩)
    (Fin.forall_fin_two.2 ⟨example_enough_roots LL hLL example_primes_dvd_level.2.2.1, example_enough_roots LL hLL example_primes_dvd_level.2.2.2.1⟩)
    (Fin.forall_fin_two.2 ⟨example_primes_gt_sixteen.1, example_primes_gt_sixteen.2⟩)

theorem exampleAdditiveChars_exist : ∃ Ps : CharT (nd2X LL hLL) (toyPrimes LL hLL), Ps.Ok :=
  additiveChars_at_T_exist (examplePrimes_ok LL hLL)
    (Fin.forall_fin_two.2 ⟨example_enough_roots LL hLL example_primes_dvd_level.2.2.2.2.1, example_enough_roots LL hLL example_primes_dvd_level.2.2.2.2.2⟩)

def toyCharacters : Chars (nd2X LL hLL) (toyPrimes LL hLL) Examples₂.R0.m := (exampleCharacters_exist LL hLL).choose

theorem exampleCharacters_ok : (toyCharacters LL hLL).Ok := (exampleCharacters_exist LL hLL).choose_spec

def toyCharacterTable : CharT (nd2X LL hLL) (toyPrimes LL hLL) := (exampleAdditiveChars_exist LL hLL).choose

def toyComplexEmbedding : (nd2X LL hLL).K →+* ℂ := sig0 ndIota LL

def ToyHeckeCondition : Prop := (toyCharacters LL hLL).HeckeEx (nd2W LL hLL) (toyComplexEmbedding LL hLL)

def toyDatum (h : ToyHeckeCondition LL hLL) : Dat where
  R := Examples₂.R0
  X := nd2X LL hLL
  sig0 := toyComplexEmbedding LL hLL
  Pr := toyPrimes LL hLL
  Ch := (toyCharacters LL hLL).ofHecke (toyComplexEmbedding LL hLL) h.choose h.choose_spec.choose
  W := nd2W LL hLL
  a := 161

end Inst

instance fin_cycNd2 : FiniteDimensional ℚ (cycQ nd2N) := finiteDimensional_cyclotomic example_level_pos

instance normal_cycNd2 : Normal ℚ (cycQ nd2N) := normal_cyclotomic nd2N

end Formalism.L2.Col
