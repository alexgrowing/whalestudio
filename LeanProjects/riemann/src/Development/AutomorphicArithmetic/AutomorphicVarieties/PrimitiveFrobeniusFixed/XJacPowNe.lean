import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.IsAdmissiblePrimeListNil
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.StickelbergerTheorem.FfsumPow
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.StickelbergerTheorem.RedRoot
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.StickelbergerTheorem.JacDvd
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.StickelbergerTheorem.Sqfree
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.StickelbergerTheorem.SplitProd

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

private theorem xJac_pow_ne {R : Type} [CommRing R] (p : ℕ) [hp : Fact p.Prime] (π : R →+* ZMod p)
    (χ : MulChar (ZMod p) R) (M d : ℕ) (hd : p - 1 = M * d)
    (hχ : ∀ x : ZMod p, x ≠ 0 → π (χ x) = x ^ d) (n : ℕ) (h : χ ^ n = 1) : M ∣ n := by
  have hp1 : 0 < p - 1 := by have := hp.out.two_le; omega
  have hd0 : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h | h
    · rw [h, mul_zero] at hd; omega
    · exact h
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have hog : orderOf g = M * d := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, ZMod.card_units, hd]
  have h2 : χ (g : ZMod p) ^ n = 1 := by
    rw [← MulChar.pow_apply_coe, h, MulChar.one_apply_coe]
  have h3 : g ^ (n * d) = 1 := by
    ext
    have := congrArg π h2
    rw [map_pow, hχ g g.ne_zero, map_one, ← pow_mul, mul_comm] at this
    simpa using this
  have h4 := orderOf_dvd_of_pow_eq_one h3
  rw [hog] at h4
  exact Nat.dvd_of_mul_dvd_mul_right hd0 h4

private theorem xJac_one (M : ℕ) [NeZero M] (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {M} ℚ K]
    (p : ℕ) [hp : Fact p.Prime] (π : 𝓞 K →+* ZMod p) (χ : MulChar (ZMod p) (𝓞 K)) (hco : p.Coprime M)
    (hχ : ∀ x : ZMod p, x ≠ 0 → χ x ^ M = 1 ∧ π (χ x) = x ^ ((p - 1) / M))
    (a b : ZMod M) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a + b ≠ 0) :
    jacobiSum (χ ^ a.val) (χ ^ b.val) ∣ (p : 𝓞 K) ∧ ∀ t : (ZMod M)ˣ,
      jacobiSum (χ ^ a.val) (χ ^ b.val) ∈ conjI M K (RingHom.ker π) t ↔ carry M (a * t) (b * t) = 0 := by
  have hz := IsCyclotomicExtension.zeta_spec M ℚ K
  have hζ : IsPrimitiveRoot hz.toInteger M := hz.toInteger_isPrimitiveRoot
  obtain ⟨hπ, d, hd⟩ := redRoot (𝓞 K) p π M _ hco hζ
  rw [hd, Nat.mul_div_cancel_left _ (NeZero.pos M)] at hχ
  have hp1 : 0 < p - 1 := by have := hp.out.two_le; omega
  have hd0 : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h | h
    · rw [h, mul_zero] at hd; omega
    · exact h
  have hne : ∀ n : ℕ, (n : ZMod M) ≠ 0 → χ ^ n ≠ 1 := by
    intro n hn h
    exact hn ((ZMod.natCast_eq_zero_iff n M).2 (xJac_pow_ne p π χ M d hd (fun x hx => (hχ x hx).2) n h))
  have hval : ∀ (c : ZMod M) (t : (ZMod M)ˣ), c ≠ 0 → 0 < (c * t).val := by
    intro c t hc
    rw [Nat.pos_iff_ne_zero, Ne, ZMod.val_eq_zero]
    exact fun h => hc ((Units.mul_left_eq_zero t).1 h)
  have hred : ∀ (c : ZMod M) (t : (ZMod M)ˣ), c ≠ 0 → ∀ x : ZMod p,
      π (sgO M K t ((χ ^ c.val) x)) = x ^ (d * (c * t).val) := by
    intro c t hc x
    have hc0 : c.val ≠ 0 := by rwa [Ne, ZMod.val_eq_zero]
    by_cases hx : x = 0
    · subst hx
      rw [MulChar.map_zero, map_zero, map_zero, zero_pow (Nat.mul_pos hd0 (hval c t hc)).ne']
    · obtain ⟨h1, h2⟩ := hχ x hx
      rw [MulChar.pow_apply' _ hc0, map_pow, sgO_apply M K t h1, ← pow_mul,
        pow_eq_pow_mod _ h1, mul_comm (t : ZMod M).val, ← ZMod.val_mul, map_pow, h2, ← pow_mul]
  refine ⟨?_, fun t => ?_⟩
  · apply jacDvd
    · exact hne _ (by simpa using ha)
    · exact hne _ (by simpa using hb)
    · rw [← pow_add]
      exact hne _ (by simpa using hab)
  · have hlt : ∀ c : ZMod M, d * c.val < p - 1 := by
      intro c
      rw [hd, mul_comm M]
      exact Nat.mul_lt_mul_of_pos_left (ZMod.val_lt c) hd0
    rw [mem_conjI, RingHom.mem_ker, jacobiSum, map_sum, map_sum]
    simp only [map_mul, hred a t ha, hred b t hb]
    rw [ffsum p _ _ (Nat.mul_pos hd0 (hval a t ha)) (hlt _) (Nat.mul_pos hd0 (hval b t hb)) (hlt _),
      hd, ← mul_add, mul_comm M, Nat.mul_lt_mul_left hd0, carry]
    split_ifs with h
    · simp only [one_ne_zero, iff_false, not_lt]; exact h
    · simp only [iff_true]; omega

private theorem xJac_step (M : ℕ) [NeZero M] (k : ℕ) (t : ZMod M) :
    t.val * (k + 1) / M = t.val * k / M + carry M (1 * t) ((k : ZMod M) * t) := by
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have ht : t.val < M := ZMod.val_lt t
  have h1 : ((k : ZMod M) * t).val = t.val * k % M := by
    rw [ZMod.val_mul, ZMod.val_natCast, Nat.mod_mul_mod, mul_comm]
  rw [mul_add, mul_one, Nat.add_div hM, Nat.div_eq_of_lt ht, Nat.mod_eq_of_lt ht, carry, h1, one_mul,
    add_zero, add_comm t.val]

private theorem xJac_sum (M : ℕ) [NeZero M] (t : ZMod M) (b : ℕ) :
    ∑ j ∈ Finset.Ico 1 b, (1 - carry M (1 * t) ((j : ZMod M) * t)) + t.val * b / M = b - 1 := by
  induction b with
  | zero => simp
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [Nat.div_eq_of_lt (ZMod.val_lt t)]
    · rw [Finset.sum_Ico_succ_top hk, xJac_step]
      have : carry M (1 * t) ((k : ZMod M) * t) ≤ 1 := by unfold carry; split_ifs <;> omega
      show ∑ j ∈ Finset.Ico 1 k, (1 - carry M (1 * t) ((j : ZMod M) * t)) + _ + _ = _
      omega

private theorem xJac_span (M : ℕ) [NeZero M] (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {M} ℚ K]
    (p : ℕ) [hp : Fact p.Prime] (π : 𝓞 K →+* ZMod p) (hco : p.Coprime M) (J : 𝓞 K) (hJ : J ∣ (p : 𝓞 K))
    (c : (ZMod M)ˣ → ℕ) (hc : ∀ t, J ∈ conjI M K (RingHom.ker π) t ↔ c t = 0) :
    Ideal.span {J} = ∏ t, conjI M K (RingHom.ker π) t ^ (1 - c t) := by
  obtain ⟨h1, h2⟩ := splitProd M K p π hco
  rw [sqfree _ _ _ (splitInj M K p π hco) h1 J (Finset.univ.filter fun t => c t = 0)
    (by rw [h2]; exact Ideal.dvd_iff_le.2 (Ideal.span_singleton_le_span_singleton.2 hJ)) (by simp [hc]), Finset.prod_filter]
  refine Finset.prod_congr rfl fun t _ => ?_
  split_ifs with h
  · simp [h]
  · rw [show 1 - c t = 0 by omega, pow_zero]

private theorem xJac_sgO (M : ℕ) [NeZero M] (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {M} ℚ K]
    (s t : (ZMod M)ˣ) (x : 𝓞 K) : sgO M K s (sgO M K t x) = sgO M K (s * t) x := by
  apply Subtype.ext
  show sg M K s (sg M K t x) = sg M K (s * t) x
  rw [map_mul]; rfl

private theorem xJac_frac {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] (P : ι → Ideal (𝓞 K))
    (e : ι → ℕ) (J : 𝓞 K) (h : Ideal.span {J} = ∏ t, P t ^ e t) :
    FractionalIdeal.spanSingleton (𝓞 K)⁰ (J : K) = ∏ t, (P t : FractionalIdeal (𝓞 K)⁰ K) ^ e t := by
  have := congrArg (FractionalIdeal.coeIdealHom (𝓞 K)⁰ K) h
  rw [map_prod] at this
  simp only [map_pow, FractionalIdeal.coeIdealHom_apply, FractionalIdeal.coeIdeal_span_singleton] at this
  exact this

theorem UpperTheory.V.ML.xJac :
    ∀ (M : ℕ) [NeZero M] (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {M} ℚ K] (b p : ℕ) [Fact p.Prime] (π : 𝓞 K →+* ZMod p) (χ : MulChar (ZMod p) (𝓞 K)), p.Coprime M → b < M →
    (∀ x : ZMod p, x ≠ 0 → χ x ^ M = 1 ∧ π (χ x) = x ^ ((p - 1) / M)) →
    IsX M K b (RingHom.ker π) (sg M K (-1) ((∏ j ∈ Finset.Ico 1 b, jacobiSum χ (χ ^ j) : 𝓞 K) : K) / ((∏ j ∈ Finset.Ico 1 b, jacobiSum χ (χ ^ j) : 𝓞 K) : K)) := by
  intro M _ K _ _ _ b p hp π χ hco hb hχ
  have key : ∀ j ∈ Finset.Ico 1 b, jacobiSum χ (χ ^ j) ∣ (p : 𝓞 K) ∧ ∀ t : (ZMod M)ˣ,
      jacobiSum χ (χ ^ j) ∈ conjI M K (RingHom.ker π) t ↔ carry M (1 * (t : ZMod M)) ((j : ZMod M) * t) = 0 := by
    intro j hj
    obtain ⟨hj1, hj2⟩ := Finset.mem_Ico.1 hj
    haveI : Fact (1 < M) := ⟨by omega⟩
    have hn : ∀ n : ℕ, 0 < n → n < M → (n : ZMod M) ≠ 0 := fun n h1 h2 h =>
      absurd (Nat.le_of_dvd h1 ((ZMod.natCast_eq_zero_iff n M).1 h)) (by omega)
    have := xJac_one M K p π χ hco hχ 1 j one_ne_zero (hn j hj1 (by omega))
      (by have := hn (1 + j) (by omega) (by omega); rwa [Nat.cast_add, Nat.cast_one] at this)
    rwa [ZMod.val_one, pow_one, ZMod.val_natCast_of_lt (by omega)] at this
  set P := conjI M K (RingHom.ker π) with hP
  set e : ZMod M → ℕ := fun t => ∑ j ∈ Finset.Ico 1 b, (1 - carry M (1 * t) ((j : ZMod M) * t)) with he
  set J : 𝓞 K := ∏ j ∈ Finset.Ico 1 b, jacobiSum χ (χ ^ j) with hJ
  have h1 : Ideal.span {J} = ∏ t : (ZMod M)ˣ, P t ^ e t := by
    rw [hJ, ← Ideal.prod_span_singleton, Finset.prod_congr rfl fun j hj =>
      xJac_span M K p π hco _ (key j hj).1 _ (key j hj).2, Finset.prod_comm]
    exact Finset.prod_congr rfl fun t _ => Finset.prod_pow_eq_pow_sum _ _ _
  have h2 : Ideal.span {sgO M K (-1) J} = ∏ t : (ZMod M)ˣ, P t ^ e (-t) := by
    rw [hJ, map_prod, ← Ideal.prod_span_singleton, Finset.prod_congr rfl fun (j : ℕ) hj =>
      xJac_span M K p π hco (sgO M K (-1) (jacobiSum χ (χ ^ j)))
        (by simpa using map_dvd (sgO M K (-1)) (key j hj).1)
        (fun t => carry M (1 * (-t : ZMod M)) ((j : ZMod M) * (-t : ZMod M)))
        (fun t => by
          rw [mem_conjI, xJac_sgO, mul_neg_one, ← mem_conjI, (key j hj).2, Units.val_neg]), Finset.prod_comm]
    exact Finset.prod_congr rfl fun t _ => Finset.prod_pow_eq_pow_sum _ _ _
  have hJ0 : J ≠ 0 := by
    rw [hJ]
    refine Finset.prod_ne_zero_iff.2 fun j hj h => ?_
    have := (key j hj).1
    rw [h, zero_dvd_iff] at this
    exact hp.out.ne_zero (by exact_mod_cast this)
  have hJK : (J : K) ≠ 0 := by exact_mod_cast hJ0
  have hs : sg M K (-1) (J : K) ≠ 0 := (map_ne_zero _).2 hJK
  refine ⟨?_, ?_⟩
  · have : sg M K (-1) (sg M K (-1) (J : K)) = J := by
      rw [← AlgEquiv.mul_apply, ← map_mul]; simp
    rw [map_div₀, this]
    field_simp
  · have h3 := xJac_frac _ _ _ h1
    have h4 : FractionalIdeal.spanSingleton (𝓞 K)⁰ (sg M K (-1) (J : K)) = _ := xJac_frac _ _ _ h2
    rw [← FractionalIdeal.spanSingleton_div_spanSingleton, h3, h4, ← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun t _ => ?_
    have hP0 : (P t : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 :=
      FractionalIdeal.coeIdeal_ne_zero.2 ((splitProd M K p π hco).1 t).ne_zero
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_sub₀ hP0]
    congr 1
    have e1 : e t + _ = _ := xJac_sum M t b
    have e2 : e (-t) + _ = _ := xJac_sum M (-t) b
    unfold th
    omega
