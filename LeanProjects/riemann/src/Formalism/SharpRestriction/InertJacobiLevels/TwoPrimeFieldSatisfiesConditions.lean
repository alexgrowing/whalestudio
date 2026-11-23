import Formalism.SharpRestriction.InertJacobiLevels.TwoPrimeFieldMemLevelOfCoprime

noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition NumberField IsDedekindDomain
open scoped Pointwise

structure HostOk (x eps Cp : ℝ) {R : Ranks} (H : Host R) : Prop where
  good : QDGood x eps H.q H.d
  split_tie : ⌊x ^ (eps / 5)⌋₊ ≤ H.splitBound
  g_win : ∀ i, Yof R x eps ≤ (H.g i : ℝ) ∧ (H.g i : ℝ) ≤ 2 * Yof R x eps
  g_norm : ∀ i, ∃ π : 𝓞 H.E, (π : H.E) ∈ H.K ∧ (π : H.E) * H.conj (π : H.E) = (H.g i : H.E)
  g_norm1 : ∀ i, ∃ π ρ : 𝓞 H.E, (π : H.E) ∈ H.K ∧ (ρ : H.E) ∈ H.K ∧
    (π : H.E) - 1 = ((H.QS * H.q * H.d : ℕ) : H.E) * ρ ∧ (π : H.E) * H.conj (π : H.E) = (H.g i : H.E)
  g_mod : ∀ i, H.g i % (H.QS * H.q * H.d) = 1
  thyp : THyp H
  g_split : ∀ k, (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E
  g_cls : ∀ i, H.cls (H.g i) = .splitK
  pde_split : (Ideal.primesOver (Ideal.span {(H.pde : ℤ)}) (𝓞 H.E)).ncard = Module.finrank ℚ H.E ∧
    (Ideal.primesOver (Ideal.span {(H.pde' : ℤ)}) (𝓞 H.E)).ncard = Module.finrank ℚ H.E
  pde_cls : H.cls H.pde = .splitK ∧ H.cls H.pde' = .splitK
  pde_log : Real.log H.pde < x ^ (eps / 3) ∧ Real.log H.pde' < x ^ (eps / 3)
  ccK_norm : Ideal.absNorm H.ccK = 1
  secondSet_card_lower_bound : H.secondSet_card_lower_bound
  secondTorsion_card_pos : 0 < H.T2.card
  secondTorsion_card_le : H.T2.card ≤ R.n0
  o_tie : (R.o : ℝ) ≤ x ^ (eps / 1000)
  QS_tie : (H.QS : ℝ) ≤ 4 * R.n * x ^ (eps / 1000)

theorem rdE_bounds {R : Ranks} (H : Host R) :
    1 ≤ H.rdE ∧ H.rdE ≤ (H.QS : ℝ) / 2 * Real.sqrt ((H.q : ℝ) * H.d) := by
  obtain ⟨hge, hle, -⟩ := factRd R H
  refine ⟨le_trans ?_ hge, hle⟩
  have hd : (1 : ℝ) ≤ Real.sqrt (H.d : ℝ) := by
    rw [Real.one_le_sqrt]; exact_mod_cast H.hyp.2.1.one_lt.le
  have he : (0 : ℝ) ≤ R.e := Nat.cast_nonneg _
  have h2 : (2 : ℝ) ^ (-(R.e : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ ((R.e : ℝ) + 1 - (2 : ℝ) ^ (-(R.e : ℝ))) :=
    Real.one_le_rpow (by norm_num) (by linarith)
  nlinarith

theorem norm_mod {R : Ranks} (H : Host R) {M T : ℕ} (hM : 0 < M) (π : 𝓞 H.E)
    (h2 : (π : H.E) * H.conj (π : H.E) = (T : H.E)) (h3 : (π - 1) ∈ Ideal.span {((M : ℕ) : 𝓞 H.E)}) :
    T ≡ 1 [MOD M] := by
  obtain ⟨ρ, hρ⟩ := Ideal.mem_span_singleton.1 h3
  have hπ : (π : H.E) = 1 + (M : H.E) * (ρ : H.E) := by
    have : ((π - 1 : 𝓞 H.E) : H.E) = (((M : ℕ) : 𝓞 H.E) * ρ : 𝓞 H.E) := by rw [hρ]
    push_cast at this
    linear_combination this
  have hint : IsIntegral ℤ (H.conj (ρ : H.E)) := map_isIntegral_int H.conj ρ.2
  set ρ' : 𝓞 H.E := ⟨H.conj (ρ : H.E), hint⟩ with hρ'
  have hρc : ((ρ' : 𝓞 H.E) : H.E) = H.conj (ρ : H.E) := rfl
  set w : 𝓞 H.E := ρ + ρ' + (M : 𝓞 H.E) * ρ * ρ' with hw
  have hwc : (w : H.E) = (ρ : H.E) + H.conj (ρ : H.E) + (M : H.E) * ρ * H.conj (ρ : H.E) := by
    rw [hw, ← hρc]; push_cast; rfl
  have key : (T : H.E) - 1 = (M : H.E) * (w : H.E) := by
    rw [← h2, hπ, hwc]
    simp only [map_add, map_mul, map_one, map_natCast]
    ring
  have hM0 : (M : H.E) ≠ 0 := by exact_mod_cast hM.ne'
  have hr : algebraMap ℚ H.E (((T : ℚ) - 1) / M) = (w : H.E) := by
    rw [map_div₀, map_sub, map_one, map_natCast, map_natCast, key, mul_div_cancel_left₀ _ hM0]
  have hi : IsIntegral ℤ (((T : ℚ) - 1) / M) := by
    rw [← isIntegral_algebraMap_iff (algebraMap ℚ H.E).injective, hr]
    exact w.2
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.1 hi
  have hMq : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  have hz' : (T : ℤ) - 1 = M * z := by
    have : (T : ℚ) - 1 = M * z := by
      have h5 : (z : ℚ) = ((T : ℚ) - 1) / M := by simpa using hz
      rw [h5]; field_simp
    exact_mod_cast this
  rw [← Int.natCast_modEq_iff]
  apply Int.ModEq.symm
  rw [Int.modEq_iff_dvd]
  exact ⟨z, by push_cast; exact hz'⟩

private theorem placesOver_ncard_of_mod {R : Ranks} (H : Host R) (p : ℕ) [Fact p.Prime] (hm : p ≡ 1 [MOD H.condN]) :
    (placesOver H.E p).ncard = Module.finrank ℚ H.E := by
  have h1 : 1 < H.condN :=
    lt_of_lt_of_le (by norm_num) (Nat.le_of_dvd (Nat.pos_of_ne_zero H.condN_ne_zero) H.two_dvd_condN)
  have h2 : p % H.condN = 1 % H.condN := hm
  rw [Nat.mod_eq_of_lt h1] at h2
  exact placesOver_ncard_of_split H p h2

theorem tnorm_facts {R : Ranks} (H : Host R) {T : ℕ} (hp : T.Prime) (h : TNorm H T) :
    T ≡ 1 [MOD H.QS * H.q * H.d * (H.g 0 * H.g 1) ^ 2] ∧ H.cls T = .splitK ∧
      T ≠ 2 ∧ T ≠ H.q ∧ T ≠ H.d ∧ (∀ i, T ≠ H.g i) ∧
      (placesOver H.E T).ncard = Module.finrank ℚ H.E := by
  obtain ⟨π, -, h2, h3⟩ := h
  have hn := H.QS_pos
  have hM : 0 < H.QS * H.q * H.d * (H.g 0 * H.g 1) ^ 2 := by
    have := H.hyp.1.pos; have := H.hyp.2.1.pos; have := (H.g_prime 0).pos; have := (H.g_prime 1).pos
    positivity
  have hmod := norm_mod H hM π h2 h3
  obtain ⟨-, a0, a1, a2, a3, -, a5⟩ := one_mod_facts H.toHostRaw hp.one_lt (hmod.of_mul_right _)
  have : Fact T.Prime := ⟨hp⟩
  have hne : ∀ p : ℕ, p ∣ H.QS * H.q * H.d * (H.g 0 * H.g 1) ^ 2 → T ≠ p := by
    rintro p hd rfl
    have h5 : T % T = 1 % T := hmod.of_dvd hd
    rw [Nat.mod_self, Nat.mod_eq_of_lt hp.one_lt] at h5
    omega
  refine ⟨hmod, cls_split_of H a0 a2 a3 a5, a1, a2, a3, fun i => ?_,
    placesOver_ncard_of_mod H T (hmod.of_mul_right _)⟩
  fin_cases i
  · exact hne _ ⟨H.QS * H.q * H.d * (H.g 0 * H.g 1 ^ 2), by simp only [Fin.zero_eta]; ring⟩
  · exact hne _ ⟨H.QS * H.q * H.d * (H.g 0 ^ 2 * H.g 1), by simp only [Fin.mk_one]; ring⟩

variable {R : Ranks} {x eps Cp CT : ℝ} (B : Base R x eps Cp CT)

namespace Base

theorem q_odd : Odd B.q := Nat.odd_iff.2 (by have := B.good.hyp.2.2.1; omega)
theorem d_odd : Odd B.d := Nat.odd_iff.2 (by have := B.good.hyp.2.2.2.1; omega)

theorem one_lt_cond : 1 < B.condN :=
  lt_of_lt_of_le (by norm_num) (Nat.le_of_dvd (Nat.pos_of_ne_zero B.condN_ne_zero) B.two_dvd_condN)

theorem facts_of_mod {g : ℕ} (hp : g.Prime) (hg : g ≡ 1 [MOD B.condN]) :
    ¬ g ∣ B.condN ∧ g ∉ B.small ∧ g ≠ 2 ∧ g ≠ B.q ∧ g ≠ B.d ∧ jacobiSym (-(B.q : ℤ)) g = 1 ∧
      jacobiSym (-(B.d : ℤ)) g = 1 :=
  one_mod_facts B.toHostRaw hp.one_lt hg

theorem first_prime_modEq_one : B.g0 ≡ 1 [MOD B.condN] := by
  obtain ⟨u, v, h⟩ := B.first_prime_norm_form; exact form_mod h
theorem second_prime_modEq_one : B.g1 ≡ 1 [MOD B.condN] := by
  obtain ⟨u, v, h⟩ := B.second_prime_norm_form; exact form_mod h

theorem mod_eq_one {g : ℕ} (hg : g ≡ 1 [MOD B.condN]) : g % (B.QS * B.q * B.d) = 1 := by
  have h1 : g % B.condN = 1 % B.condN := hg
  rw [Nat.mod_eq_of_lt B.one_lt_cond] at h1
  exact h1

end Base

theorem twoPrimeField_split_of_modEq (u0 : R.A) (ex : Finset ℕ) {p : ℕ} (hp : p.Prime)
    (hm : p ≡ 1 [MOD B.condN]) :
    (host2 B u0 ex).cls p = .splitK ∧
      (placesOver (host2 B u0 ex).E p).ncard = Module.finrank ℚ (host2 B u0 ex).E ∧
      (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 (host2 B u0 ex).E)).ncard =
        Module.finrank ℚ (host2 B u0 ex).E := by
  obtain ⟨-, h1, -, h2, h3, -, h5⟩ := B.facts_of_mod hp hm
  have : Fact p.Prime := ⟨hp⟩
  have hs := placesOver_ncard_of_mod (host2 B u0 ex) p hm
  exact ⟨cls_split_of (host2 B u0 ex) h1 h2 h3 h5, hs, (primesOver_ncard _ p hp).trans hs⟩

theorem twoPrimeField_satisfies_conditions (u0 : R.A) (ex : Finset ℕ) : HostOk x eps Cp (host2 B u0 ex) where
  good := B.good
  split_tie := le_refl _
  g_win := by intro i; fin_cases i; exacts [B.first_prime_in_window, B.second_prime_in_window]
  g_norm := by
    intro i; fin_cases i
    · obtain ⟨u, v, h⟩ := B.first_prime_norm_form
      obtain ⟨π, h1, h2, -⟩ := norm_form (host2 B u0 ex) u v B.g0 _ h
      exact ⟨π, h1, h2⟩
    · obtain ⟨u, v, h⟩ := B.second_prime_norm_form
      obtain ⟨π, h1, h2, -⟩ := norm_form (host2 B u0 ex) u v B.g1 _ h
      exact ⟨π, h1, h2⟩
  g_norm1 := by
    intro i; fin_cases i
    · obtain ⟨u, v, h⟩ := B.first_prime_norm_form
      exact norm_form' (host2 B u0 ex) u v B.g0 _ h
    · obtain ⟨u, v, h⟩ := B.second_prime_norm_form
      exact norm_form' (host2 B u0 ex) u v B.g1 _ h
  g_mod := by intro i; fin_cases i; exacts [B.mod_eq_one B.first_prime_modEq_one, B.mod_eq_one B.second_prime_modEq_one]
  thyp := by
    refine ⟨fun k => ?_, B.bb, fun k => ?_⟩
    · fin_cases k; exacts [B.mod_eq_one B.first_prime_modEq_one, B.mod_eq_one B.second_prime_modEq_one]
    · fin_cases k
      · obtain ⟨-, -, h1, -, -, -, h5⟩ := B.facts_of_mod B.first_prime_isPrime B.first_prime_modEq_one; exact ⟨h1, h5⟩
      · obtain ⟨-, -, h1, -, -, -, h5⟩ := B.facts_of_mod B.second_prime_isPrime B.second_prime_modEq_one; exact ⟨h1, h5⟩
  g_split := by
    intro k; fin_cases k
    · exact (twoPrimeField_split_of_modEq B u0 ex B.first_prime_isPrime B.first_prime_modEq_one).2.1
    · exact (twoPrimeField_split_of_modEq B u0 ex B.second_prime_isPrime B.second_prime_modEq_one).2.1
  g_cls := by
    intro k; fin_cases k
    · exact (twoPrimeField_split_of_modEq B u0 ex B.first_prime_isPrime B.first_prime_modEq_one).1
    · exact (twoPrimeField_split_of_modEq B u0 ex B.second_prime_isPrime B.second_prime_modEq_one).1
  pde_split := ⟨(twoPrimeField_split_of_modEq B u0 ex B.pde_prime (B.pde_mod.of_mul_left _)).2.2,
    (twoPrimeField_split_of_modEq B u0 ex B.pde'_prime (B.pde'_mod.of_mul_left _)).2.2⟩
  pde_cls := ⟨(twoPrimeField_split_of_modEq B u0 ex B.pde_prime (B.pde_mod.of_mul_left _)).1,
    (twoPrimeField_split_of_modEq B u0 ex B.pde'_prime (B.pde'_mod.of_mul_left _)).1⟩
  pde_log := B.pde_log
  ccK_norm := Ideal.absNorm_top
  secondSet_card_lower_bound := B.T2_card
  o_tie := B.o_tie
  QS_tie := B.QS_tie
  secondTorsion_card_pos := by
    have h := B.T2_card
    have hn0 : 0 < R.n0 := addOrderOf_pos _
    have hL : (0 : ℝ) < B.Lw := by exact_mod_cast (lt_of_lt_of_le two_pos B.two_le_Lw)
    have : (0 : ℝ) < B.T2.card := lt_of_lt_of_le (by positivity) h
    exact_mod_cast this
  secondTorsion_card_le := by
    have hsub : B.T2 ⊆ Finset.range R.n0 := by
      intro s hs
      have h1 := B.second_set_range s hs
      have h2 := B.two_le_Lw
      have h3 : s ≤ 4 * B.Lw * s := Nat.le_mul_of_pos_left s (by omega)
      exact Finset.mem_range.2 (by omega)
    have h4 := Finset.card_le_card hsub
    rw [Finset.card_range] at h4
    exact h4

theorem twoPrimeField_levelPrimes_split (u0 : R.A) (ex : Finset ℕ) (hex : ∀ p ∈ ex, (host2 B u0 ex).cls p = .splitK) :
    ∀ p ∈ (host2 B u0 ex).levelPrimes, (host2 B u0 ex).cls p = .splitK := by
  intro p hp
  have ok := twoPrimeField_satisfies_conditions B u0 ex
  have hp' : p ∈ ({B.g0, B.g1, B.pde, B.pde'} ∪ ex : Finset ℕ) := twoPrimeField_level_subset B u0 ex hp
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hp'
  rcases hp' with (rfl | rfl | rfl | rfl) | h
  · exact ok.g_cls 0
  · exact ok.g_cls 1
  · exact ok.pde_cls.1
  · exact ok.pde_cls.2
  · exact hex p h

def Base.MT : ℕ := B.condN * (B.g0 * B.g1) ^ 2

theorem host2_TNorm_and_cls_splitK_of_prime_eq (u0 : R.A) (ex : Finset ℕ) {T : ℕ} (hp : T.Prime) {u v : ℤ}
    (hT : (T : ℤ) = (1 + (B.MT : ℕ) * u) ^ 2 + B.d * ((B.MT : ℕ) * v) ^ 2) :
    TNorm (host2 B u0 ex) T ∧ (host2 B u0 ex).cls T = .splitK :=
  ⟨tnorm_of (host2 B u0 ex) u v T B.MT hT rfl,
    (twoPrimeField_split_of_modEq B u0 ex hp ((form_mod hT).of_mul_right _)).1⟩

section Indep

variable (u0 u0' : R.A) (ex ex' : Finset ℕ)

theorem twoPrimeField_base_unit : (host2 B u0 ex).u0 = u0 := rfl
theorem twoPrimeField_mem_level {T : ℕ} (h : T ∈ ex) (hc : Nat.Coprime T B.QS) : T ∈ (host2 B u0 ex).levelPrimes :=
  twoPrimeField_mem_level_of_coprime B u0 ex h hc
theorem twoPrimeField_modulus : (host2 B u0 ex).q = B.q := rfl
theorem twoPrimeField_discriminant : (host2 B u0 ex).d = B.d := rfl
theorem twoPrimeField_generators : (host2 B u0 ex).g = ![B.g0, B.g1] := rfl
theorem twoPrimeField_firstPrime : (host2 B u0 ex).pde = B.pde := rfl
theorem twoPrimeField_secondPrime : (host2 B u0 ex).pde' = B.pde' := rfl
theorem twoPrimeField_torsionSet : (host2 B u0 ex).TT = B.TT := rfl
theorem host2_T2_eq : (host2 B u0 ex).T2 = B.T2 := rfl
theorem twoPrimeField_weightLattice : (host2 B u0 ex).Lw = B.Lw := rfl
theorem twoPrimeField_errorConstant : (host2 B u0 ex).CT2 = CT := rfl
theorem twoPrimeField_splitBound : (host2 B u0 ex).splitBound = ⌊x ^ (eps / 5)⌋₊ := rfl
theorem twoPrimeField_field_eq : (host2 B u0 ex).E = B.E := rfl
theorem twoPrimeField_axioms : (host2 B u0 ex).toHostAx = B.toHostAx := rfl
theorem twoPrimeField_smallModulus : (host2 B u0 ex).QS = B.QS := rfl
theorem twoPrimeField_rootDiscriminant : (host2 B u0 ex).rdE = B.rd := rfl
theorem twoPrimeField_twistedNorm_iff (T : ℕ) : TNorm (host2 B u0 ex) T ↔ TNorm (host2 B u0' ex') T := Iff.rfl
theorem twoPrimeField_class_eq (p : ℕ) : (host2 B u0 ex).cls p = (host2 B u0' ex').cls p := rfl

end Indep

end Formalism.MainNotions.Inhab

end
