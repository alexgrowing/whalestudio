import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyValExtOfOverLa

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CharDepth GlobalTheory.FactorDepth

namespace GlobalTheory.IsoCols

theorem exists_norm_eq_neg_one {k : Type} [Field k] [Finite k] (σ : k →+* k) (hσ : ∀ x, σ (σ x) = x)
    {y : k} (hy : y - σ y ≠ 0) : ∃ a, a * σ a = -1 := by
  classical
  by_cases h2 : ringChar k = 2
  · haveI : CharP k 2 := ringChar.of_eq h2
    exact ⟨1, by rw [map_one, one_mul, CharTwo.neg_eq]⟩
  let k0 : Subfield k := RingHom.eqLocusField σ (RingHom.id k)
  haveI : Fintype k0 := Fintype.ofFinite _
  have hδ : σ (y - σ y) = -(y - σ y) := by rw [map_sub, hσ]; ring
  let d : k0 := ⟨(y - σ y) ^ 2, by
    show σ _ = _
    rw [map_pow, hδ]; simp only [RingHom.id_apply]; ring⟩
  have hd : d ≠ 0 := fun h => pow_ne_zero 2 hy (congrArg Subtype.val h)
  have hc : ringChar k0 ≠ 2 := by
    intro h
    haveI : CharP k0 2 := ringChar.of_eq h
    haveI : CharP k 2 := charP_of_injective_ringHom (f := k0.subtype) Subtype.val_injective 2
    exact h2 (ringChar.eq k 2)
  obtain ⟨a, b, hab⟩ := FiniteField.exists_root_sum_quadratic
    (f := (Polynomial.X ^ 2 + Polynomial.C 1 : Polynomial k0)) (g := Polynomial.C (-d) * Polynomial.X ^ 2)
    (Polynomial.degree_X_pow_add_C (by norm_num) _) (Polynomial.degree_C_mul_X_pow 2 (neg_ne_zero.2 hd))
    (FiniteField.odd_card_of_char_ne_two hc)
  have h : (a : k) ^ 2 + 1 + -(y - σ y) ^ 2 * (b : k) ^ 2 = 0 := by
    have := congrArg Subtype.val hab
    simpa [d] using this
  have ha : σ a = a := a.2
  have hb : σ b = b := b.2
  refine ⟨a + b * (y - σ y), ?_⟩
  rw [map_add, map_mul, hδ, ha, hb]
  linear_combination h

theorem exists_pair_seq {R : Type} [CommRing R] (bar : R ≃+* R) (hbb : ∀ x, bar (bar x) = x) (w : Ideal R)
    [hw : w.IsMaximal] [Finite (R ⧸ w)] {y : R} (hy : y - bar y ∉ w) :
    ∃ u a : ℕ → R, (∀ k, u k - 1 ∈ w ^ k) ∧ (∀ k, a (k + 1) - a k ∈ w ^ k) ∧
      ∀ k, u k * bar (u k) + a k * bar (a k) ∈ w ^ k := by
  by_cases hs : w.comap bar = w
  · have hmem : ∀ x ∈ w, bar x ∈ w := fun x hx => by rw [← hs] at hx; exact hx
    letI := Ideal.Quotient.field w
    let σ : R ⧸ w →+* R ⧸ w := Ideal.Quotient.lift w ((Ideal.Quotient.mk w).comp bar.toRingHom)
      fun x hx => Ideal.Quotient.eq_zero_iff_mem.2 (hmem x hx)
    have hσ : ∀ x, σ (Ideal.Quotient.mk w x) = Ideal.Quotient.mk w (bar x) := fun x => rfl
    have hσσ : ∀ x, σ (σ x) = x := fun x => by
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [hσ, hσ, hbb]
    have hy' : Ideal.Quotient.mk w y - σ (Ideal.Quotient.mk w y) ≠ 0 := by
      rw [hσ, ← map_sub]; exact fun h => hy (Ideal.Quotient.eq_zero_iff_mem.1 h)
    obtain ⟨a0, ha0⟩ := exists_norm_eq_neg_one σ hσσ hy'
    obtain ⟨a0, rfl⟩ := Ideal.Quotient.mk_surjective a0
    obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective (I := w)
      (Ideal.Quotient.mk w y / (Ideal.Quotient.mk w y - σ (Ideal.Quotient.mk w y)))
    have ht1 : 1 - t - bar t ∈ w := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_sub, ← hσ, ht, map_div₀, map_sub, hσσ, map_one,
        ← neg_sub (Ideal.Quotient.mk w y), div_neg]
      field_simp
      ring
    let a : ℕ → R := fun n => Nat.rec a0 (fun _ x => x * (1 + (1 + x * bar x) * t)) n
    have has : ∀ n, a (n + 1) = a n * (1 + (1 + a n * bar (a n)) * t) := fun n => rfl
    have key : ∀ n, 1 + a n * bar (a n) ∈ w ^ (n + 1) := by
      intro n
      induction n with
      | zero =>
        rw [zero_add, pow_one, ← Ideal.Quotient.eq_zero_iff_mem, map_add, map_mul, ← hσ]
        show _ + Ideal.Quotient.mk w a0 * σ (Ideal.Quotient.mk w a0) = 0
        rw [ha0]; simp
      | succ n ih =>
        have ih1 : 1 + a n * bar (a n) ∈ w := Ideal.pow_le_self (Nat.succ_ne_zero n) ih
        have e : 1 + a (n + 1) * bar (a (n + 1)) = (1 + a n * bar (a n)) * ((1 - t - bar t) +
            (1 + a n * bar (a n)) * (t + bar t + a n * bar (a n) * t * bar t)) := by
          simp only [has, map_mul, map_add, map_one, hbb]; ring
        rw [e, pow_succ w (n + 1)]
        exact Ideal.mul_mem_mul ih (w.add_mem ht1 (w.mul_mem_right _ ih1))
    refine ⟨fun _ => 1, a, fun k => by simp, fun k => ?_, fun k => ?_⟩
    · have e : a (k + 1) - a k = (1 + a k * bar (a k)) * (a k * t) := by rw [has]; ring
      rw [e]
      exact Ideal.mul_mem_right _ _ (Ideal.pow_le_pow_right (Nat.le_succ k) (key k))
    · simpa using Ideal.pow_le_pow_right (Nat.le_succ k) (key k)
  · have hm : (w.comap bar).IsMaximal := Ideal.comap_isMaximal_of_equiv bar
    have hco : ∀ k, ∃ u ∈ (w.comap bar) ^ k, u - 1 ∈ w ^ k := fun k => by
      have h : (w.comap bar) ^ k ⊔ w ^ k = ⊤ := Ideal.pow_sup_pow_eq_top (hm.coprime_of_ne hw hs)
      obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 (h ▸ Submodule.mem_top (x := (1 : R)))
      exact ⟨u, hu, by rw [← huv]; simpa using hv⟩
    choose u hu hu1 using hco
    refine ⟨u, fun _ => 0, hu1, fun k => by simp, fun k => ?_⟩
    simp only [zero_mul, add_zero]
    exact Ideal.mul_mem_left _ _ (Ideal.le_comap_pow bar k (hu k))

theorem exists_pair {R V : Type} [CommRing R] [IsDedekindDomain R] [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] (bar : R ≃+* R)
    (hbb : ∀ x, bar (bar x) = x) (φ : R →+* V) [((IsLocalRing.maximalIdeal V).comap φ).IsMaximal]
    [Finite (R ⧸ (IsLocalRing.maximalIdeal V).comap φ)] {y : R}
    (hy : y - bar y ∉ (IsLocalRing.maximalIdeal V).comap φ) {q : R} (hq : φ q ≠ 0) :
    ∃ α : V, ∀ N : ℕ, ∃ u a : R, (∃ z, φ u = 1 + φ q ^ N * z) ∧ (∃ z, φ a = α + φ q ^ N * z) ∧
      u * bar u + a * bar a ∈ Ideal.span {q ^ N} := by
  set m := IsLocalRing.maximalIdeal V
  set w := m.comap φ
  obtain ⟨u, a, hu, ha, hh⟩ := exists_pair_seq bar hbb w hy
  have hφ : ∀ k, ∀ x ∈ w ^ k, φ x ∈ m ^ k := fun k x hx => Ideal.le_comap_pow φ k hx
  obtain ⟨α, hα⟩ := IsPrecomplete.prec' (I := m) (fun k => φ (a k)) (by
    intro i j hij
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
    induction j, hij using Nat.le_induction with
    | base => simp
    | succ j hij ih =>
      have h1 := Ideal.pow_le_pow_right hij (hφ j _ (ha j))
      have := (m ^ i).sub_mem ih h1
      rw [map_sub] at this
      convert this using 1; ring)
  refine ⟨α, fun N => ?_⟩
  have hq0 : q ≠ 0 := fun h => hq (by rw [h, map_zero])
  obtain ⟨J, hJ, hI⟩ := Ideal.eq_prime_pow_mul_coprime (I := Ideal.span {q ^ N})
    (by simpa [Ideal.span_singleton_eq_bot] using fun h => absurd h hq0) w
  set k0 := Multiset.count w (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {q ^ N}))
  obtain ⟨k1, hk1⟩ : ∃ k1, m ^ k1 ≤ Ideal.span {φ q ^ N} := by
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
    obtain ⟨k1, h⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible (s := Ideal.span {φ q ^ N})
      (by simpa [Ideal.span_singleton_eq_bot] using fun h => absurd h hq) hϖ
    exact ⟨k1, by rw [h, ← Ideal.span_singleton_pow, ← hϖ.maximalIdeal_eq]⟩
  let k := k0 + k1
  have hk : ∀ x ∈ m ^ k, ∃ z, x = φ q ^ N * z := fun x hx =>
    Ideal.mem_span_singleton.1 (hk1 (Ideal.pow_le_pow_right (Nat.le_add_left _ _) hx))
  have h : J ⊔ w ^ k = ⊤ := Ideal.sup_pow_eq_top (by rw [sup_comm, hJ])
  obtain ⟨v, hv, v', hv', hvv⟩ := Submodule.mem_sup.1 (h ▸ Submodule.mem_top (x := (1 : R)))
  have hαk : φ (a k) - α ∈ m ^ k := by
    have := hα k
    rwa [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at this
  refine ⟨v * u k, v * a k, ?_, ?_, ?_⟩
  · obtain ⟨z, hz⟩ := hk _ (hφ k _ ((w ^ k).sub_mem (hu k) (Ideal.mul_mem_right (u k) _ hv')))
    refine ⟨z, ?_⟩
    rw [← hz, ← map_one φ, ← map_add]
    congr 1
    linear_combination (u k) * hvv
  · obtain ⟨z, hz⟩ := hk _ ((m ^ k).sub_mem hαk (hφ k _ (Ideal.mul_mem_right (a k) _ hv')))
    refine ⟨z, ?_⟩
    have := congrArg φ hvv
    rw [← hz]
    simp only [map_mul, map_add, map_one] at this ⊢
    linear_combination (φ (a k)) * this
  · rw [hI]
    have e : v * u k * bar (v * u k) + v * a k * bar (v * a k) =
        (u k * bar (u k) + a k * bar (a k)) * (v * bar v) := by
      simp only [map_mul]; ring
    rw [e]
    exact Ideal.mul_mem_mul (Ideal.pow_le_pow_right (Nat.le_add_right _ _) (hh k)) (Ideal.mul_mem_right _ _ hv)

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem bar_bar (H : Host E) (x : 𝓞 E) : H.bar (H.bar x) = x := by
  apply RingOfIntegers.ext
  rw [H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply]

theorem exists_sub_bar_notMem (H : Host E) {w : Ideal (𝓞 E)} (hw : w ≠ ⊤) : ∃ y, y - H.bar y ∉ w := by
  by_contra hn
  push Not at hn
  haveI := H.unram
  have e : ∀ x, IsCMField.ringOfIntegersComplexConj E x = H.bar x := fun x => by
    apply RingOfIntegers.ext
    rw [H.bar_eq]; simp
  have h := Algebra.FormallyUnramified.ext_of_iInf (R := 𝓞 (maximalRealSubfield E)) w
    (Ideal.iInf_pow_eq_bot_of_isDomain w hw) (g₁ := AlgHom.id _ (𝓞 E))
    (g₂ := (IsCMField.ringOfIntegersComplexConj E).toAlgHom)
    (fun x => Ideal.Quotient.eq.2 (by simpa [e] using hn x))
  apply IsCMField.complexConj_ne_one E
  ext x
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (𝓞 E) x
  have h1 : ∀ a : 𝓞 E, IsCMField.complexConj E (algebraMap _ E a) = algebraMap _ E a := fun a => by
    have := DFunLike.congr_fun h a
    exact (H.bar_eq a).symm.trans (congrArg _ (this.trans (e a)).symm)
  rw [map_div₀, h1, h1, AlgEquiv.one_apply]

theorem exists_lift (T : CDVR) (ψ : 𝓞 E →+* T.Fr) : ∃ φ : 𝓞 E →+* T.V, ∀ x, algebraMap T.V T.Fr (φ x) = ψ x := by
  have h : ∀ x, ∃ z : T.V, algebraMap T.V T.Fr z = ψ x := fun x =>
    IsIntegrallyClosed.algebraMap_eq_of_integral
      ((RingOfIntegers.isIntegral x).map_of_comp_eq (Int.castRingHom T.V) ψ (RingHom.ext_int _ _))
  choose φ hφ using h
  have inj := IsFractionRing.injective T.V T.Fr
  exact ⟨{ toFun := φ
           map_one' := inj (by simp [hφ])
           map_mul' := fun x y => inj (by simp [hφ])
           map_zero' := inj (by simp [hφ])
           map_add' := fun x y => inj (by simp [hφ]) }, hφ⟩

variable {H : Host E} {l : Level H}

theorem exists_isIsoCols (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) (p : ℕ) [Fact p.Prime]
    (hp : ¬ IsUnit (p : T.V)) (τ : E →+* ℂ) {i n : ℕ} (g : Fin (2 * i) → Fin n) (hg : Function.Injective g) :
    ∃ B : Fin i → Fin n → T.V, IsIsoCols c T io p τ (Set.range g) B := by
  classical
  obtain ⟨φ, hφ⟩ := exists_lift T (io.comp (embK c τ))
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hb : (IsLocalRing.maximalIdeal T.V).comap φ ≠ ⊥ := fun h => by
    have : (p : 𝓞 E) ∈ (IsLocalRing.maximalIdeal T.V).comap φ := by
      rw [Ideal.mem_comap, map_natCast]; exact hp
    rw [h, Ideal.mem_bot] at this
    exact hp0 (by exact_mod_cast this)
  haveI hm : ((IsLocalRing.maximalIdeal T.V).comap φ).IsMaximal := Ideal.IsPrime.isMaximal inferInstance hb
  haveI : Finite (𝓞 E ⧸ (IsLocalRing.maximalIdeal T.V).comap φ) := Ideal.finiteQuotientOfFreeOfNeBot _ hb
  obtain ⟨y, hy⟩ := exists_sub_bar_notMem H hm.ne_top
  obtain ⟨α, hα⟩ := exists_pair H.bar (bar_bar H) φ hy (q := p) (by rw [map_natCast]; exact_mod_cast hp0)
  let c1 : Fin i → Fin n := fun b => g ⟨b, by omega⟩
  let c2 : Fin i → Fin n := fun b => g ⟨i + b, by omega⟩
  have h11 : ∀ b b', c1 b = c1 b' ↔ b = b' := fun b b' => by simp [c1, hg.eq_iff, Fin.ext_iff]
  have h22 : ∀ b b', c2 b = c2 b' ↔ b = b' := fun b b' => by simp [c2, hg.eq_iff, Fin.ext_iff]
  have h12 : ∀ b b', c1 b ≠ c2 b' := fun b b' h => by
    have := congrArg Fin.val (hg h)
    simp only at this
    omega
  have h21 : ∀ b b', c2 b ≠ c1 b' := fun b b' => (h12 b' b).symm
  have hS : ∀ b j, j ∉ Set.range g → j ≠ c1 b ∧ j ≠ c2 b := fun b j hj =>
    ⟨fun h => hj ⟨_, h.symm⟩, fun h => hj ⟨_, h.symm⟩⟩
  refine ⟨fun b j => if j = c1 b then 1 else if j = c2 b then α else 0, fun b j hj => ?_, ⟨c1, ?_⟩, fun N => ?_⟩
  · simp [hS b j hj]
  · have : (Matrix.of fun b b' => if c1 b' = c1 b then (1 : T.V) else if c1 b' = c2 b then α else 0) = 1 := by
      ext b b'
      simp [h11, h12, Matrix.one_apply, eq_comm]
    rw [this, Matrix.det_one]
    exact isUnit_one
  obtain ⟨u, a, ⟨z1, hz1⟩, ⟨z2, hz2⟩, hh⟩ := hα N
  rw [map_natCast] at hz1 hz2
  refine ⟨fun b j => if j = c1 b then u else if j = c2 b then a else 0, fun b j hj => ?_, fun b j => ?_,
    fun b b' => ?_⟩
  · simp [hS b j hj]
  · dsimp only
    split_ifs
    · exact ⟨z1, by rw [← hz1, hφ]; rfl⟩
    · exact ⟨z2, by rw [← hz2, hφ]; rfl⟩
    · exact ⟨0, by simp⟩
  · dsimp only
    rw [Fintype.sum_eq_add (c1 b) (c2 b) (h12 b b) fun j hj => by simp [hj.1, hj.2]]
    by_cases hbb : b = b'
    · subst hbb
      simpa [h21] using hh
    · simp [h11, h12, h21, h22, hbb]

theorem exists_isCols : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (p : ℕ) [Fact p.Prime] (la : PointsOfFlagModel.abelian₂ p c) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la.1 T.V io e → ∀ (cx : Lt1 Dw → ℕ) (n : ℕ), (∑ f : Lt1 Dw, if cx f ≠ 0 then 2 * rk f else 0) ≤ n → ∃ B : ∀ f : Lt1 Dw, Fin (rk f) → Fin n → T.V, IsCols c T io p cx B := by
  intro E _ _ _ H Dw l _ c p _ la T io e ho cx n hn
  classical
  have hp := not_isUnit_of_overLa la ho
  obtain ⟨blk⟩ : Nonempty ((Σ f : {f : Lt1 Dw // cx f ≠ 0}, Fin (2 * rk f.1)) ↪ Fin n) := by
    apply Function.Embedding.nonempty_of_card_le
    rw [Fintype.card_sigma, Fintype.card_fin]
    simp only [Fintype.card_fin]
    rw [← Finset.sum_filter] at hn
    rwa [← Finset.sum_subtype (Finset.univ.filter fun f => cx f ≠ 0) (by simp) (fun f : Lt1 Dw => 2 * rk f)]
  choose B hB using fun f : {f : Lt1 Dw // cx f ≠ 0} =>
    exists_isIsoCols c T io p hp f.1.1 (fun j => blk ⟨f, j⟩) fun j j' h => by simpa using blk.injective h
  refine ⟨fun f => if h : cx f ≠ 0 then B ⟨f, h⟩ else 0, blk, fun f => ?_⟩
  simp only [dif_pos f.2]
  exact hB f

end GlobalTheory.IsoCols
