import Mathlib
import Formalism.PairingDivisors.StatementA
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor

open NumberField IsDedekindDomain GlobalTheory.CMVal

namespace GlobalTheory.CMVal.OrderUnits

theorem prime_not_mem_sq {E : Type} [Field E] [NumberField E] {p : ℕ} (hp : p.Prime) (hd : ¬ (p : ℤ) ∣ discr E)
    (w : HeightOneSpectrum (𝓞 E)) (hv : (p : 𝓞 E) ∈ w.asIdeal) : (p : 𝓞 E) ∉ w.asIdeal ^ 2 := by
  obtain ⟨P, hP, hP0⟩ := w
  have he : P.ramificationIdx ℤ = 1 := by
    have h1 := (NumberField.not_dvd_discr_iff_forall_mem E (𝓞 E) (Nat.prime_iff_prime_int.mp hp)).1 hd P hP (by simpa using hv)
    have := hP.isMaximal hP0
    have : (P.under ℤ).IsMaximal := inferInstance
    have hne : P.under ℤ ≠ ⊥ := by
      intro h0
      have h1 : (p : ℤ) ∈ P.under ℤ := by rw [Ideal.under_def, Ideal.mem_comap]; simpa using hv
      rw [h0] at h1
      exact hp.ne_zero (by simpa using h1)
    have : Finite (ℤ ⧸ P.under ℤ) := Ideal.finiteQuotientOfFreeOfNeBot _ hne
    have : Finite (P.under ℤ).ResidueField := inferInstance
    exact Ideal.ramificationIdx_eq_one_iff.2 h1
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  have hmap : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(p : ℤ)}) = Ideal.span {(p : 𝓞 E)} := by
    rw [Ideal.map_span]; simp
  have hle : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(p : ℤ)}) ≤ P := by
    rw [hmap, Ideal.span_le]; simpa using hv
  have : P.LiesOver (Ideal.span {(p : ℤ)}) :=
    ⟨hmax.eq_of_le (Ideal.comap_ne_top _ hP.ne_top) (Ideal.map_le_iff_le_comap.mp hle)⟩
  have hb : Ideal.span {(p : ℤ)} ≠ ⊥ := by simpa using hp.ne_zero
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx (Ideal.span {(p : ℤ)}) P hb] at he
  intro h2
  refine (Ideal.ramificationIdx'_ne_one_iff hle).2 ?_ he
  rw [hmap, Ideal.span_le]
  simpa using h2

theorem pow_first_order {R : Type} [CommRing R] (t : R) (i : ℕ) : ∃ r, (1 + t) ^ i = 1 + i * t + t ^ 2 * r := by
  induction i with
  | zero => exact ⟨0, by simp⟩
  | succ i ih =>
    obtain ⟨r, hr⟩ := ih
    exact ⟨r + i + t * r, by rw [pow_succ, hr]; push_cast; ring⟩

theorem geom_first_order {R : Type} [CommRing R] (t : R) (n : ℕ) :
    ∃ r, ∑ i ∈ Finset.range n, (1 + t) ^ i = n + (n.choose 2 : ℕ) * t + t ^ 2 * r := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨r, hr⟩ := ih
    obtain ⟨s, hs⟩ := pow_first_order t n
    refine ⟨r + s, ?_⟩
    rw [Finset.sum_range_succ, hr, hs, Nat.choose_succ_succ' n 1, Nat.choose_one_right]
    push_cast; ring

theorem root_of_unity_eq_one {R : Type} [CommRing R] [IsDomain R] {P : Ideal R} (hP : P ≠ ⊤) {l : ℕ} (hl : l.Prime) (hl2 : l ≠ 2)
    (hlP : (l : R) ∈ P) (hlP2 : (l : R) ∉ P ^ 2) {ζ : R} (hζ : IsOfFinOrder ζ) (h1 : ζ - 1 ∈ P) : ζ = 1 := by
  by_contra hne
  have hn : orderOf ζ ≠ 1 := fun h => hne (orderOf_eq_one_iff.1 h)
  obtain ⟨p, hp, m, hm⟩ := Nat.exists_prime_and_dvd hn
  have hpos := hζ.orderOf_pos
  have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp [hm] at hpos)
  have hη1 : ζ ^ m ≠ 1 := pow_ne_one_of_lt_orderOf hm0.ne' (by rw [hm]; nlinarith [hp.two_le])
  have hηp : (ζ ^ m) ^ p = 1 := by rw [← pow_mul, mul_comm, ← hm, pow_orderOf_eq_one]
  have ht : ζ ^ m - 1 ∈ P := by
    obtain ⟨s, hs⟩ := sub_one_dvd_pow_sub_one ζ m
    rw [hs]; exact P.mul_mem_right _ h1
  have hsum : ∑ i ∈ Finset.range p, (ζ ^ m) ^ i = 0 := by
    have := mul_geom_sum (ζ ^ m) p
    rw [hηp, sub_self] at this
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hη1)
  obtain ⟨r, hr⟩ := geom_first_order (ζ ^ m - 1) p
  rw [add_sub_cancel, hsum] at hr
  set t := ζ ^ m - 1
  have hpe : (p : R) = -((p.choose 2 : ℕ) * t) - t ^ 2 * r := by linear_combination -hr
  have hpP : (p : R) ∈ P := by
    rw [hpe]
    exact sub_mem (neg_mem (P.mul_mem_left _ ht)) (P.mul_mem_right _ (P.pow_mem_of_mem ht 2 two_pos))
  have hpl : p = l := by
    by_contra h
    have hc : IsCoprime (p : R) (l : R) := Nat.Coprime.cast ((Nat.coprime_primes hp hl).2 h)
    obtain ⟨a, b, hab⟩ := hc
    exact hP ((Ideal.eq_top_iff_one P).2 (hab ▸ add_mem (P.mul_mem_left _ hpP) (P.mul_mem_left _ hlP)))
  subst hpl
  obtain ⟨k, hk⟩ := hp.dvd_choose_self two_ne_zero (lt_of_le_of_ne hp.two_le (Ne.symm hl2))
  apply hlP2
  rw [hpe, hk]
  refine sub_mem (neg_mem ?_) (Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow ht 2))
  rw [sq]
  push_cast
  exact Ideal.mul_mem_mul (P.mul_mem_right _ hlP) ht

theorem orderC_units (E : Type) [Field E] [NumberField E] [IsCMField E] (𝔣 c : Ideal (OF E)) (h𝔣 : IsBaseCond 𝔣) (hc : 𝔣 ∣ c)
    (x : E) (hx0 : x ≠ 0) (hx : x ∈ orderC c) (hx' : x⁻¹ ∈ orderC c) : ∃ u : (OF E)ˣ, x = algebraMap (OF E) E u := by
  obtain ⟨h0, h1, h⟩ := h𝔣
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal 𝔣 h1
  have hM0 : M ≠ ⊥ := fun h => h0 (le_bot_iff.1 (h ▸ hle))
  obtain ⟨⟨P, -, -, hP, -⟩, -, l, hl, hl2, hlv, hd, -⟩ := h ⟨M, hM.isPrime, hM0⟩ (Ideal.dvd_iff_le.2 hle)
  have hP' : P.asIdeal.comap (algebraMap (OF E) (𝓞 E)) = M := hP
  have hlP : (l : 𝓞 E) ∈ P.asIdeal := by
    have : (l : OF E) ∈ P.asIdeal.comap (algebraMap (OF E) (𝓞 E)) := by rw [hP']; exact hlv
    simpa using this
  have hcP : Ideal.map (algebraMap (OF E) (𝓞 E)) c ≤ P.asIdeal :=
    Ideal.map_le_iff_le_comap.2 (hP' ▸ (Ideal.le_of_dvd hc).trans hle)
  obtain ⟨a, b, hb, hab⟩ := mem_orderC.1 hx
  obtain ⟨a', b', -, hab'⟩ := mem_orderC.1 hx'
  have e1 : x = algebraMap (𝓞 E) E (algebraMap (OF E) (𝓞 E) a + b) := by rw [hab, map_add]; rfl
  have e2 : x⁻¹ = algebraMap (𝓞 E) E (algebraMap (OF E) (𝓞 E) a' + b') := by rw [hab', map_add]; rfl
  have hu : (algebraMap (OF E) (𝓞 E) a + b) * (algebraMap (OF E) (𝓞 E) a' + b') = 1 := by
    apply FaithfulSMul.algebraMap_injective (𝓞 E) E
    rw [map_mul, ← e1, ← e2, mul_inv_cancel₀ hx0, map_one]
  let u : (𝓞 E)ˣ := Units.mkOfMulEqOne _ _ hu
  have huv : (u : 𝓞 E) = algebraMap (OF E) (𝓞 E) a + b := rfl
  have hbc : IsCMField.ringOfIntegersComplexConj E b ∈ Ideal.map (algebraMap (OF E) (𝓞 E)) c := by
    have : Ideal.map (algebraMap (OF E) (𝓞 E)) c ≤
        (Ideal.map (algebraMap (OF E) (𝓞 E)) c).comap (IsCMField.ringOfIntegersComplexConj E) := by
      rw [Ideal.map_le_iff_le_comap]
      intro y hy
      rw [Ideal.mem_comap, Ideal.mem_comap, AlgEquiv.commutes]
      exact Ideal.mem_map_of_mem _ hy
    exact this hb
  have hcu : ((IsCMField.unitsComplexConj E u : (𝓞 E)ˣ) : 𝓞 E) =
      algebraMap (OF E) (𝓞 E) a + IsCMField.ringOfIntegersComplexConj E b := by
    have : ((IsCMField.unitsComplexConj E u : (𝓞 E)ˣ) : 𝓞 E) = IsCMField.ringOfIntegersComplexConj E u := rfl
    rw [this, huv, map_add, AlgEquiv.commutes]
  let ζ : (𝓞 E)ˣ := u * (IsCMField.unitsComplexConj E u)⁻¹
  have hfin : IsOfFinOrder ζ := (IsCMField.unitsMulComplexConjInv E u).2
  have hfin' : IsOfFinOrder (ζ : 𝓞 E) := (Units.coeHom (𝓞 E)).isOfFinOrder hfin
  have hζ : (ζ : 𝓞 E) - 1 ∈ P.asIdeal := by
    have : (ζ : 𝓞 E) - 1 = (b - IsCMField.ringOfIntegersComplexConj E b) * ↑(IsCMField.unitsComplexConj E u)⁻¹ := by
      have h3 := (IsCMField.unitsComplexConj E u).mul_inv
      rw [hcu] at h3
      simp only [ζ, Units.val_mul, huv]
      linear_combination h3
    rw [this]
    exact P.asIdeal.mul_mem_right _ (hcP (sub_mem hb hbc))
  have hone : ζ = 1 := Units.ext (root_of_unity_eq_one P.isPrime.ne_top hl hl2 hlP (prime_not_mem_sq hl hd P hlP) hfin' hζ)
  have hreal := (IsCMField.unitsComplexConj_eq_self_iff E u).1 (mul_inv_eq_one.1 hone).symm
  obtain ⟨v, hv⟩ := (IsCMField.mem_realUnits_iff E u).1 hreal
  refine ⟨v, ?_⟩
  rw [e1, ← huv, ← hv]
  rfl

end GlobalTheory.CMVal.OrderUnits
