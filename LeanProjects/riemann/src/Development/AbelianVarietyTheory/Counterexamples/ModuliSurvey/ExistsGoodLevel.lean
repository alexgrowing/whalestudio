import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses

noncomputable section

namespace GlobalTheory.GlobalModelGuards

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

theorem exists_place (p : ℕ) (hp : p.Prime) : ∃ W : ValuationSubring ℂ, (p : ℂ) ∈ W.nonunits := by
  have hne : (Ideal.span {(p : (⊥ : Subring ℂ))}) ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    intro hu
    obtain ⟨v, hv⟩ := hu.exists_right_inv
    obtain ⟨n, hn⟩ := Subring.mem_bot.1 v.2
    have h1 : ((p : ℤ) * n : ℤ) = 1 := by
      have := congrArg Subtype.val hv
      simp only [Subring.coe_mul, Subring.coe_natCast, Subring.coe_one] at this
      rw [← hn] at this
      exact_mod_cast this
    have := Int.isUnit_iff_natAbs_eq.1 (IsUnit.of_mul_eq_one _ h1)
    simp at this
    exact hp.one_lt.ne' this
  obtain ⟨W, -, hW⟩ := Ideal.image_subset_nonunits_valuationSubring _ hne
  exact ⟨W, hW ⟨p, Ideal.mem_span_singleton_self _, by simp⟩⟩

theorem exists_incl {l : Level H} (c : Coeff l) (W : ValuationSubring ℂ) :
    ∃! b : 𝓞 c.F →+* c.V W, ∀ x, ((b x : c.V W) : c.F) = (x : c.F) := by
  have hm : ∀ x : 𝓞 c.F, algebraMap (𝓞 c.F) c.F x ∈ c.V W := by
    intro x
    have hi : IsIntegral (c.V W) (x : c.F) := (RingOfIntegers.isIntegral_coe x).tower_top
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hi
    have : (y : c.F) = x := hy
    change (x : c.F) ∈ c.V W
    rw [← this]; exact y.2
  refine ⟨(algebraMap (𝓞 c.F) c.F).codRestrict (c.V W).toSubring hm, fun x => rfl, fun b hb => ?_⟩
  ext x
  exact congrArg _ (hb x)

theorem not_isUnit {l : Level H} (c : Coeff l) (W : ValuationSubring ℂ) (p : ℕ) (hW : (p : ℂ) ∈ W.nonunits) :
    ¬ IsUnit (p : c.V W) := by
  intro hu
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  have hvW : ((v : c.F) : ℂ) ∈ W := v.2
  have h1 : (p : ℂ) * ((v : c.F) : ℂ) = 1 := by
    have := congrArg (fun z : c.V W => ((z : c.F) : ℂ)) hv
    simpa using this
  rw [ValuationSubring.mem_nonunits_iff] at hW
  have h2 := (W.valuation_le_one_iff _).2 hvW
  have h3 := congrArg W.valuation h1
  rw [map_mul, map_one] at h3
  have : W.valuation p * W.valuation ((v : c.F) : ℂ) < 1 := mul_lt_one_of_lt_of_le hW h2
  exact this.ne h3

theorem exists_lift {l : Level H} {Xo : Moduli D l} {c : Coeff l} (W : ValuationSubring ℂ)
    (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (b : 𝓞 c.F →+* c.V W)
    (hb : ∀ x, ((b x : c.V W) : c.F) = (x : c.F)) :
    ∃ a : Xo.XF c ⟶ pullback Y.s (spMap b), a ≫ pullback.fst _ _ = Y.j := by
  have hc : (c.V W).subtype.comp b = algebraMap (𝓞 c.F) c.F := RingHom.ext hb
  refine ⟨pullback.lift Y.j (pullback.snd _ _ ≫ spMap (c.V W).subtype) ?_, pullback.lift_fst _ _ _⟩
  rw [Model.j, Category.assoc, pullback.condition, ← Category.assoc, Y.jQ_over, Category.assoc,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp, hc]

theorem goodAt_of_coprime (l : Level H) (a b : ℕ) (ha : 3 ≤ a) (hb : 3 ≤ b) (hab : a.Coprime b)
    (hM : l.M = a * b) (p : ℕ) (hp : p.Prime) : l.GoodAt p := by
  unfold Level.GoodAt
  have hM0 : l.M ≠ 0 := by have := l.three_le; omega
  have key : ∀ c, 3 ≤ c → c ∣ l.M → ¬ p ∣ c → 3 ≤ l.M / p ^ l.M.factorization p := fun c hc hd hn =>
    hc.trans (Nat.le_of_dvd (Nat.ordCompl_pos p hM0) (Nat.dvd_ordCompl_of_dvd_not_dvd hd hn))
  by_cases h : p ∣ a
  · refine key b hb (hM ▸ dvd_mul_left _ _) fun h' => hp.one_lt.ne' ?_
    exact Nat.eq_one_of_dvd_coprimes hab h h'
  · exact key a ha (hM ▸ dvd_mul_right _ _) h

theorem not_goodAt_pow (l : Level H) (p k : ℕ) (hp : p.Prime) (hM : l.M = p ^ k) : ¬ l.GoodAt p := by
  unfold Level.GoodAt
  rw [hM, Nat.factorization_pow, Finsupp.smul_apply, hp.factorization_self, smul_eq_mul, mul_one,
    Nat.div_self (pow_pos hp.pos k)]
  omega

theorem exists_good_level (H : Host E) : ∃ l : Level H, l.A = 1 ∧ ∀ p : ℕ, p.Prime → l.GoodAt p := by
  have hd := H.d_mod
  obtain ⟨e, he⟩ : ∃ e, H.d = 16 * e + 7 := ⟨H.d / 16, by omega⟩
  have hrt : H.rt = 2 * H.w0 - 1 := by rw [H.two_weight_eq_one_add_root]; ring
  have hbar : H.bar H.rt = -H.rt := by
    have h2 : (H.bar H.rt) ^ 2 = H.rt ^ 2 := by rw [← map_pow, H.rt_sq]; simp
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h2 with h | h
    · exfalso
      have h3 : IsCMField.complexConj E (H.rt : E) = H.rt := by rw [← H.bar_eq, h]
      have φ : E →+* ℂ := Classical.choice inferInstance
      have h4 := IsCMField.complexEmbedding_complexConj E φ (H.rt : E)
      rw [h3] at h4
      have h5 : φ (H.rt : E) ^ 2 = -(H.d : ℂ) := by
        have := congrArg (fun z : 𝓞 E => φ (z : E)) H.rt_sq
        simpa using this
      have h6 : (φ (H.rt : E)).im = 0 := Complex.conj_eq_iff_im.1 h4.symm
      have h7 := congrArg Complex.re h5
      simp [sq, h6] at h7
      have : (0 : ℝ) < H.d := by exact_mod_cast (by omega : 0 < H.d)
      nlinarith [mul_self_nonneg (φ (H.rt : E)).re]
    · exact h
  set r := H.rt with hr
  have hr2 : r ^ 2 = -(H.d : 𝓞 E) := H.rt_sq
  set N₁ : ℕ := H.d + 4 with hN₁
  set N₂ : ℕ := 4 * N₁ ^ 2 + H.d with hN₂
  have hcop : N₁.Coprime N₂ := by
    have h1 : N₁.Coprime H.d := by
      rw [hN₁, Nat.coprime_self_add_left]
      exact (Nat.coprime_pow_left_iff (by norm_num : 0 < 2) 2 H.d).2 ((Nat.coprime_two_left).2 ⟨8 * e + 3, by omega⟩)
    have : N₂ = H.d + N₁ * (4 * N₁) := by rw [hN₂]; ring
    rw [this, Nat.coprime_add_mul_left_right]; exact h1
  have o1 : Odd N₁ := ⟨8 * e + 5, by omega⟩
  have o2 : Odd N₂ := ⟨2 * N₁ ^ 2 + 8 * e + 3, by omega⟩
  let α : 𝓞 E := (2 + r) * (2 * N₁ + r)
  have hα : H.bar α = (2 - r) * (2 * N₁ - r) := by
    simp only [α, map_mul, map_add, map_natCast, map_ofNat, hbar]; ring
  have n1 : (2 + r) * (2 - r) = (N₁ : 𝓞 E) := by rw [hN₁]; push_cast; linear_combination -hr2
  have n2 : (2 * N₁ + r) * (2 * N₁ - r) = (N₂ : 𝓞 E) := by rw [hN₂]; push_cast; linear_combination -hr2
  have cZ : ∀ a b : ℕ, a.Coprime b → IsCoprime (a : 𝓞 E) (b : 𝓞 E) := fun a b h => Nat.Coprime.cast h
  have c4 : ∀ n : ℕ, Odd n → IsCoprime (n : 𝓞 E) (4 : 𝓞 E) := fun n hn => by
    have := cZ n 4 ((Nat.coprime_pow_right_iff (by norm_num : 0 < 2) n 2).2 (Nat.coprime_two_right.2 hn))
    simpa using this
  have c12 := cZ _ _ hcop
  have k1 : IsCoprime (2 + r) (2 - r) := by
    have := c4 _ o1
    rw [← n1] at this
    have h := this.of_mul_left_left
    have e4 : (4 : 𝓞 E) = (2 - r) + (2 + r) * 1 := by ring
    rw [e4] at h
    exact h.of_add_mul_left_right
  have k2 : IsCoprime (2 * (N₁ : 𝓞 E) + r) (2 * N₁ - r) := by
    have := (c4 _ o2).mul_right c12.symm
    rw [← n2] at this
    have h := this.of_mul_left_left
    have e4 : (4 : 𝓞 E) * N₁ = (2 * N₁ - r) + (2 * N₁ + r) * 1 := by ring
    rw [e4] at h
    exact h.of_add_mul_left_right
  have k3 : IsCoprime (2 + r) (2 * (N₁ : 𝓞 E) - r) := by
    have := c12
    rw [← n2] at this
    conv at this => lhs; rw [← n1]
    exact this.of_mul_left_left.of_mul_right_right
  have k4 : IsCoprime (2 * (N₁ : 𝓞 E) + r) (2 - r) := by
    have := c12.symm
    rw [← n2] at this
    conv at this => rhs; rw [← n1]
    exact this.of_mul_left_left.of_mul_right_right
  have hmap : (Ideal.span {α}).map (H.bar : 𝓞 E →+* 𝓞 E) = Ideal.span {H.bar α} := by
    rw [Ideal.map_span, Set.image_singleton]; rfl
  have hmem : α ∈ Algebra.adjoin ℤ {H.w0} := by
    have hw : H.w0 ∈ Algebra.adjoin ℤ {H.w0} := Algebra.subset_adjoin rfl
    have hr' : r ∈ Algebra.adjoin ℤ {H.w0} := by
      rw [hrt]; exact sub_mem (mul_mem (ofNat_mem _ 2) hw) (one_mem _)
    exact mul_mem (add_mem (ofNat_mem _ 2) hr') (add_mem (mul_mem (ofNat_mem _ 2) (natCast_mem _ _)) hr')
  let l : Level H :=
    { M := N₁ * N₂
      three_le := by nlinarith [show 3 ≤ N₁ by omega, show 3 ≤ N₂ by omega]
      odd := o1.mul o2
      Mb := Ideal.span {α}
      fromK := le_antisymm (Ideal.span_mono (by
          rintro x rfl; exact ⟨Ideal.mem_span_singleton_self _, hmem⟩))
        (Ideal.span_le.2 fun x hx => hx.1)
      prod := by
        rw [hmap, Ideal.span_singleton_mul_span_singleton, hα]
        congr 2
        push_cast
        rw [← n2]
        conv_rhs => lhs; rw [← n1]
        simp only [α]; ring
      coprime := by
        rw [hmap, ← Ideal.isCoprime_iff_sup_eq, Ideal.isCoprime_span_singleton_iff, hα]
        exact (k1.mul_right k3).mul_left (k4.mul_right k2)
      A := 1
      A_pos := one_pos }
  exact ⟨l, rfl, goodAt_of_coprime l N₁ N₂ (by omega) (by omega) hcop rfl⟩

theorem exists_prime_eq {l : Level H} (c : Coeff l) (W : ValuationSubring ℂ) (p : ℕ) (hp : p.Prime)
    (hW : (p : ℂ) ∈ W.nonunits) [NumberField c.F] :
    ∃ v : IsDedekindDomain.HeightOneSpectrum (𝓞 c.F), (p : 𝓞 c.F) ∈ v.asIdeal ∧
      v.valuationSubringAtPrime c.F = c.V W := by
  obtain ⟨b, hb, -⟩ := exists_incl c W
  have hn := not_isUnit c W p hW
  have hpm : (p : 𝓞 c.F) ∈ (IsLocalRing.maximalIdeal (c.V W)).comap b := by
    rw [Ideal.mem_comap, map_natCast]; exact hn
  let v : IsDedekindDomain.HeightOneSpectrum (𝓞 c.F) :=
    ⟨(IsLocalRing.maximalIdeal (c.V W)).comap b, inferInstance, fun h => by
      rw [h, Ideal.mem_bot] at hpm
      exact hp.ne_zero (by exact_mod_cast hpm)⟩
  refine ⟨v, hpm, ?_⟩
  haveI : IsLocalization v.asIdeal.primeCompl (v.valuationSubringAtPrime c.F) :=
    Localization.subalgebra.isLocalization_ofField c.F v.asIdeal.primeCompl v.asIdeal.primeCompl_le_nonZeroDivisors
  haveI : IsDiscreteValuationRing (v.valuationSubringAtPrime c.F) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 c.F) v.ne_bot _
  refine ValuationSubring.eq_of_le_of_ne_top _ ?_ ?_
  · intro x hx
    obtain ⟨⟨a, s⟩, h⟩ := IsLocalization.surj v.asIdeal.primeCompl (⟨x, hx⟩ : v.valuationSubringAtPrime c.F)
    have hs : IsUnit (b s) := by
      by_contra h'
      exact s.2 h'
    obtain ⟨u, hu⟩ := hs.exists_right_inv
    have h1 : x * ((s : 𝓞 c.F) : c.F) = (a : c.F) := congrArg Subtype.val h
    have h2 : ((s : 𝓞 c.F) : c.F) * (u : c.F) = 1 := by
      rw [← hb]; exact congrArg Subtype.val hu
    have : x = ((b a * u : c.V W) : c.F) := by
      push_cast
      rw [hb, ← h1, mul_assoc, h2, mul_one]
    rw [this]; exact (b a * u).2
  · intro h
    apply hn
    have hp0 : (p : c.F) ≠ 0 := by exact_mod_cast hp.ne_zero
    refine IsUnit.of_mul_eq_one ⟨(p : c.F)⁻¹, h ▸ ValuationSubring.mem_top _⟩ (Subtype.ext ?_)
    simp [hp0]

end GlobalTheory.GlobalModelGuards
