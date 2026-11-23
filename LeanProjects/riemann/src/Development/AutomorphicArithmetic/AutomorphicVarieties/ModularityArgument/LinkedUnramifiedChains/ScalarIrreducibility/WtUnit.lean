import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.ComplY
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormEmbeddingIntegerLeOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousExtensionAdicCompletion

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.W

namespace UpperTheory.V.J.Wu

section Ball

variable {l : ℕ} [Fact l.Prime]

theorem norm_le_one_of_near {u : Qbar l} {r : ℝ} (hr : r ≤ 1) (h : ‖u - 1‖ ≤ r) : ‖u‖ ≤ 1 := by
  have e : u = (u - 1) + 1 := by ring
  rw [e]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (h.trans hr) (by simp))

theorem near_mul {u v : Qbar l} {r : ℝ} (hr : r ≤ 1) (hu : ‖u - 1‖ ≤ r) (hv : ‖v - 1‖ ≤ r) :
    ‖u * v - 1‖ ≤ r := by
  have e : u * v - 1 = (u - 1) * v + (v - 1) := by ring
  rw [e]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ hv)
  rw [norm_mul]
  calc ‖u - 1‖ * ‖v‖ ≤ ‖u - 1‖ * 1 := by
        gcongr
        exact norm_le_one_of_near hr hv
    _ ≤ r := by simpa using hu

theorem near_pow {u : Qbar l} {r : ℝ} (hr : r ≤ 1) (hu : ‖u - 1‖ ≤ r) (n : ℕ) : ‖u ^ n - 1‖ ≤ r := by
  induction n with
  | zero => simpa using (norm_nonneg _).trans hu
  | succ n ih => rw [pow_succ]; exact near_mul hr ih hu

theorem ball_lt : ((l : ℝ)⁻¹) ^ 2 < (l : ℝ)⁻¹ := by
  have hl : (2 : ℝ) ≤ l := by exact_mod_cast (Fact.out : l.Prime).two_le
  have h0 : 0 < (l : ℝ)⁻¹ := by positivity
  have h1 : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  nlinarith

theorem ball_le : ((l : ℝ)⁻¹) ^ 2 ≤ 1 := by
  have hl : (2 : ℝ) ≤ l := by exact_mod_cast (Fact.out : l.Prime).two_le
  have h1 : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  exact ball_lt.le.trans h1.le

theorem eq_one_of_pow_eq_one {u : Qbar l} (hu : ‖u - 1‖ ≤ ((l : ℝ)⁻¹) ^ 2) {n : ℕ} (hn : 0 < n)
    (h : u ^ n = 1) : u = 1 := by
  by_contra hne
  have hfin : IsOfFinOrder u := isOfFinOrder_iff_pow_eq_one.2 ⟨n, hn, h⟩
  have ho : orderOf u ≠ 0 := hfin.orderOf_pos.ne'
  have ho1 : orderOf u ≠ 1 := by simpa [orderOf_eq_one_iff] using hne
  have hp : (orderOf u).minFac.Prime := Nat.minFac_prime ho1
  have hpd : (orderOf u).minFac ∣ orderOf u := Nat.minFac_dvd _
  obtain ⟨p, hpe⟩ : ∃ p, p = (orderOf u).minFac := ⟨_, rfl⟩
  rw [← hpe] at hp hpd
  obtain ⟨v, hve⟩ : ∃ v, v = u ^ (orderOf u / p) := ⟨_, rfl⟩
  have hv : orderOf v = p := by rw [hve]; exact orderOf_pow_orderOf_div ho hpd
  have hv1 : v ≠ 1 := fun e => hp.one_lt.ne' (by rw [← hv, e, orderOf_one])
  have hvp : v ^ p = 1 := by rw [← hv]; exact pow_orderOf_eq_one v
  have hnear : ‖v - 1‖ ≤ ((l : ℝ)⁻¹) ^ 2 := by rw [hve]; exact near_pow ball_le hu _
  have hS : ∑ i ∈ Finset.range p, v ^ i = 0 := by
    have := geom_sum_mul v p
    rw [hvp, sub_self] at this
    exact (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 hv1)
  have hd : (p : Qbar l) = -∑ i ∈ Finset.range p, (v ^ i - 1) := by
    simp [Finset.sum_sub_distrib, hS]
  have hn1 : ‖(p : Qbar l)‖ ≤ ((l : ℝ)⁻¹) ^ 2 := by
    rw [hd, norm_neg]
    exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
      fun i _ => near_pow ball_le hnear i
  have hn2 : (l : ℝ)⁻¹ ≤ ‖(p : Qbar l)‖ := by
    have e : (p : Qbar l) = algebraMap ℚ_[l] (Qbar l) (p : ℚ_[l]) := by simp
    rw [e, norm_algebraMap']
    by_cases hpl : p = l
    · subst hpl
      rw [Padic.norm_p]
    · have h1 : ‖(p : ℚ_[l])‖ = 1 :=
        Padic.norm_natCast_eq_one_iff.2 ((Nat.coprime_primes Fact.out hp).2 (Ne.symm hpl))
      rw [h1]
      have hl : (2 : ℝ) ≤ l := by exact_mod_cast (Fact.out : l.Prime).two_le
      exact (inv_lt_one_of_one_lt₀ (by linarith)).le
  linarith [ball_lt (l := l)]

theorem norm_int_le_one {F : Type} [Field F] [NumberField F] (c : F →+* Qbar l) (x : 𝓞 F) :
    ‖c x‖ ≤ 1 := by
  have h1 : IsIntegral ℤ (c x) := (RingOfIntegers.isIntegral_coe x).map c.toIntAlgHom
  have h : IsIntegral ℤ_[l] (c x) := h1.tower_top
  have hi : IsIntegral ℚ_[l] (c x) := Algebra.IsIntegral.isIntegral _
  have h0 : ‖c x‖ = spectralValue (minpoly ℚ_[l] (c x)) := rfl
  rw [h0, spectralValue_le_one_iff (minpoly.monic hi)]
  intro n
  rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, Polynomial.coeff_map]
  exact PadicInt.norm_le_one _

end Ball

section Place

variable {F : Type} [Field F] [NumberField F] {l : ℕ} [Fact l.Prime] {w : Plc F}

theorem emb_val_lt (j : Emb l w) {y : w.adicCompletion F} (hy : Valued.v y < 1) : ‖j.1 y‖ < 1 := by
  have h2 := (j.2.tendsto 0).comp (Valued.tendsto_zero_pow_of_v_lt_one hy)
  rw [map_zero] at h2
  exact tendsto_pow_atTop_nhds_zero_iff_norm_lt_one.1 (h2.congr fun m => map_pow _ _ _)

theorem emb_lt (j : Emb l w) {x : 𝓞 F} (hx : x ∈ w.asIdeal) :
    ‖j.1 (algebraMap F (w.adicCompletion F) (x : F))‖ < 1 := by
  refine emb_val_lt j ?_
  rw [show algebraMap F (w.adicCompletion F) (x : F) = ((x : F) : w.adicCompletion F) from rfl,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact (w.valuation_lt_one_iff_mem x).2 hx

theorem emb_lt_iff (j : Emb l w) (x : 𝓞 F) :
    ‖j.1 (algebraMap F (w.adicCompletion F) (x : F))‖ < 1 ↔ x ∈ w.asIdeal := by
  refine ⟨fun h => ?_, emb_lt j⟩
  by_contra hx
  obtain ⟨y, i, hi, e⟩ := w.isMaximal.exists_inv hx
  let c : F →+* Qbar l := j.1.comp (algebraMap F (w.adicCompletion F))
  have h1 : ‖c ((y : F) * (x : F))‖ < 1 := by
    rw [map_mul, norm_mul]
    calc ‖c y‖ * ‖c x‖ ≤ 1 * ‖c x‖ := by
          gcongr
          exact norm_int_le_one c y
      _ < 1 := by
          rw [one_mul]
          exact h
  have h2 : ‖c (i : F)‖ < 1 := emb_lt j hi
  have e' : c ((y : F) * (x : F)) + c (i : F) = 1 := by
    rw [← map_add, ← map_one c]
    congr 1
    exact_mod_cast congrArg (fun t : 𝓞 F => (t : F)) e
  have h3 := IsUltrametricDist.norm_add_le_max (c ((y : F) * (x : F))) (c (i : F))
  rw [e', norm_one] at h3
  exact absurd h3 (not_le.2 (max_lt h1 h2))

theorem emb_val_eq (j : Emb l w) {y : w.adicCompletion F} (hy : ‖j.1 y‖ = 1) : Valued.v y = 1 := by
  rcases lt_trichotomy (Valued.v y) 1 with h | h | h
  · exact absurd hy (emb_val_lt j h).ne
  · exact h
  · have hy0 : y ≠ 0 := fun e => by simp [e] at hy
    have h1 : Valued.v y⁻¹ < 1 := by
      rw [map_inv₀]
      exact inv_lt_one_of_one_lt₀ h
    have h2 := emb_val_lt j h1
    rw [map_inv₀, norm_inv, hy, inv_one] at h2
    exact absurd h2 (lt_irrefl _)

theorem liesOver (hl : ((l : ℕ) : 𝓞 F) ∈ w.asIdeal) : w.asIdeal.LiesOver (Ideal.span {(l : ℤ)}) := by
  haveI := w.isMaximal
  have hp : (Ideal.span {(l : ℤ)}).IsMaximal := by
    refine PrincipalIdealRing.isMaximal_of_irreducible ?_
    exact (Nat.prime_iff_prime_int.1 (Fact.out : l.Prime)).irreducible
  refine ⟨hp.eq_of_le (Ideal.IsPrime.ne_top inferInstance) ?_⟩
  rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]
  simpa using hl

theorem norm_data (hl : ((l : ℕ) : 𝓞 F) ∈ w.asIdeal) :
    ∃ φ : ℚ_[l] →+* w.adicCompletion F, (∀ (τ : Emb l w) (c : ℚ_[l]), τ.1 (φ c) = algebraMap ℚ_[l] (Qbar l) c) ∧
      Nonempty (Emb l w) ∧ Finite (Emb l w) ∧
      ∀ z : w.adicCompletion F, ∃ c : ℚ_[l], ∏ᶠ τ : Emb l w, τ.1 z = algebraMap ℚ_[l] (Qbar l) c := by
  haveI := liesOver hl
  obtain ⟨-, φ, -, hφ, -⟩ := KStar.Ram.existsUnique_padic_hom w l
  letI : Algebra ℚ_[l] (w.adicCompletion F) := φ.toAlgebra
  haveI : ContinuousSMul ℚ_[l] (w.adicCompletion F) := continuousSMul_of_algebraMap _ _ hφ
  haveI : FiniteDimensional ℚ_[l] (w.adicCompletion F) := (KStar.Ram.finrank_compl w l).1
  haveI : CharZero (w.adicCompletion F) := φ.charZero_iff φ.injective |>.1 inferInstance
  have hcomp : ∀ (τ : Emb l w) (c : ℚ_[l]), τ.1 (φ c) = algebraMap ℚ_[l] (Qbar l) c := fun τ c => by
    have := (Padic.denseRange_ratCast l).equalizer (g := fun x => τ.1 (φ x)) (h := algebraMap ℚ_[l] (Qbar l))
      (τ.2.comp hφ) (continuous_algebraMap _ _) (by
        funext q
        simp only [Function.comp_apply, map_ratCast])
    exact congrFun this c
  have hc : ∀ σ : w.adicCompletion F →ₐ[ℚ_[l]] Qbar l, Continuous σ := fun σ =>
    LinearMap.continuous_of_finiteDimensional σ.toLinearMap
  let e : (w.adicCompletion F →ₐ[ℚ_[l]] Qbar l) ≃ Emb l w :=
    { toFun := fun σ => ⟨σ, hc σ⟩
      invFun := fun τ => { τ.1 with commutes' := hcomp τ }
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  refine ⟨φ, hcomp, ⟨e (IsAlgClosed.lift)⟩, Finite.of_equiv _ e, fun z => ⟨Algebra.norm ℚ_[l] z, ?_⟩⟩
  rw [Algebra.norm_eq_prod_embeddings ℚ_[l] (Qbar l) z, ← finprod_eq_prod_of_fintype,
    ← finprod_comp_equiv e]
  rfl

end Place

section Unit

variable {F : Type} [Field F] [NumberField F] {l : ℕ} [Fact l.Prime] {w : Plc F}

theorem norm_eq_one_of_near {u : Qbar l} (h : ‖u - 1‖ ≤ ((l : ℝ)⁻¹) ^ 2) : ‖u‖ = 1 := by
  have hl : (2 : ℝ) ≤ l := by exact_mod_cast (Fact.out : l.Prime).two_le
  have h1 : ‖u - 1‖ < 1 := h.trans_lt (ball_lt.trans (inv_lt_one_of_one_lt₀ (by linarith)))
  have e : (1 : Qbar l) = u + -(u - 1) := by ring
  have h2 : (1 : ℝ) ≤ max ‖u‖ ‖u - 1‖ := by
    have := IsUltrametricDist.norm_add_le_max u (-(u - 1))
    rwa [← e, norm_one, norm_neg] at this
  have h3 : 1 ≤ ‖u‖ := by
    rcases le_max_iff.1 h2 with h4 | h4
    · exact h4
    · exact absurd h4 (not_le.2 h1)
  exact le_antisymm (norm_le_one_of_near ball_le h) h3

theorem exists_unit (hl : ((l : ℕ) : 𝓞 F) ∈ w.asIdeal) (x : 𝓞 F) (τ₁ τ₂ : Emb l w)
    (hne : τ₁.1 (algebraMap F (w.adicCompletion F) (x : F)) ≠ τ₂.1 (algebraMap F (w.adicCompletion F) (x : F))) :
    ∃ y : (w.adicCompletion F)ˣ, Valued.v (y : w.adicCompletion F) = 1 ∧
      ∏ᶠ τ : Emb l w, τ.1 (y : w.adicCompletion F) = 1 ∧
      ∀ (τ : Emb l w) (m : ℕ), 0 < m → τ.1 (y : w.adicCompletion F) ^ m ≠ 1 := by
  obtain ⟨φ, hφ, ⟨τ₀⟩, hfin, hN⟩ := norm_data hl
  haveI := hfin
  letI := Fintype.ofFinite (Emb l w)
  obtain ⟨z, hze⟩ : ∃ z : w.adicCompletion F, z = 1 + (l : w.adicCompletion F) ^ 2 * algebraMap F _ (x : F) := ⟨_, rfl⟩
  have hlnorm : ‖((l : ℕ) : Qbar l)‖ = (l : ℝ)⁻¹ := by
    have e : ((l : ℕ) : Qbar l) = algebraMap ℚ_[l] (Qbar l) ((l : ℕ) : ℚ_[l]) := by simp
    rw [e, norm_algebraMap', Padic.norm_p]
  have hz : ∀ τ : Emb l w, ‖τ.1 z - 1‖ ≤ ((l : ℝ)⁻¹) ^ 2 := fun τ => by
    have e : τ.1 z - 1 = ((l : ℕ) : Qbar l) ^ 2 * (τ.1.comp (algebraMap F (w.adicCompletion F))) (x : F) := by
      rw [hze]
      simp
    rw [e, norm_mul, norm_pow, hlnorm]
    have := norm_int_le_one (τ.1.comp (algebraMap F (w.adicCompletion F))) x
    have h0 : (0 : ℝ) ≤ ((l : ℝ)⁻¹) ^ 2 := by positivity
    nlinarith
  have hz1 : ∀ τ : Emb l w, ‖τ.1 z‖ = 1 := fun τ => norm_eq_one_of_near (hz τ)
  have hz0 : z ≠ 0 := fun e => by
    have := hz1 τ₀
    simp [e] at this
  obtain ⟨c, hc⟩ := hN z
  rw [finprod_eq_prod_of_fintype] at hc
  have hcn : ‖algebraMap ℚ_[l] (Qbar l) c‖ = 1 := by
    rw [← hc, norm_prod]
    exact Finset.prod_eq_one fun τ _ => hz1 τ
  have hc0 : algebraMap ℚ_[l] (Qbar l) c ≠ 0 := fun e => by simp [e] at hcn
  have hφ0 : φ c ≠ 0 := fun e => hc0 (by rw [← hφ τ₀ c, e, map_zero])
  obtain ⟨d, hd⟩ : ∃ d, d = Fintype.card (Emb l w) := ⟨_, rfl⟩
  have hdpos : 0 < d := by
    rw [hd]
    exact Fintype.card_pos_iff.2 ⟨τ₀⟩
  have hy : ∀ τ : Emb l w, τ.1 (z ^ d * (φ c)⁻¹) = τ.1 z ^ d * (algebraMap ℚ_[l] (Qbar l) c)⁻¹ := fun τ => by
    rw [map_mul, map_pow, map_inv₀, hφ]
  have hy0 : z ^ d * (φ c)⁻¹ ≠ 0 := mul_ne_zero (pow_ne_zero _ hz0) (inv_ne_zero hφ0)
  refine ⟨Units.mk0 _ hy0, ?_, ?_, fun τ m hm e => ?_⟩
  · refine emb_val_eq τ₀ ?_
    rw [Units.val_mk0, hy, norm_mul, norm_pow, hz1, norm_inv, hcn]
    simp
  · rw [Units.val_mk0, finprod_eq_prod_of_fintype]
    simp only [hy]
    rw [Finset.prod_mul_distrib, Finset.prod_pow, ← hc, Finset.prod_const, Finset.card_univ, ← hd, ← mul_pow,
      mul_inv_cancel₀ (by rw [hc]; exact hc0), one_pow]
  · have hy1 : (z ^ d * (φ c)⁻¹) ^ m = 1 := τ.1.injective (by rw [map_pow, map_one]; simpa using e)
    rw [mul_pow, inv_pow, mul_inv_eq_one₀ (pow_ne_zero _ hφ0), ← pow_mul] at hy1
    have h1 : ∀ τ : Emb l w, τ.1 z ^ (d * m) = algebraMap ℚ_[l] (Qbar l) c ^ m := fun τ => by
      rw [← map_pow, hy1, map_pow, hφ]
    have hz2 : τ₂.1 z ≠ 0 := fun e => by
      have := hz1 τ₂
      simp [e] at this
    have hu : ‖τ₁.1 z / τ₂.1 z - 1‖ ≤ ((l : ℝ)⁻¹) ^ 2 := by
      have e1 : τ₁.1 z / τ₂.1 z - 1 = ((τ₁.1 z - 1) + -(τ₂.1 z - 1)) / τ₂.1 z := by
        field_simp
        ring
      rw [e1, norm_div, hz1, div_one]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hz _) ?_)
      rw [norm_neg]
      exact hz _
    have hup : (τ₁.1 z / τ₂.1 z) ^ (d * m) = 1 := by
      rw [div_pow, h1, h1, div_self (pow_ne_zero _ hc0)]
    have h2 := eq_one_of_pow_eq_one hu (Nat.mul_pos hdpos hm) hup
    have h3 : τ₁.1 z = τ₂.1 z := (div_eq_one_iff_eq hz2).1 h2
    apply hne
    rw [hze] at h3
    simp only [map_add, map_one, map_mul, map_pow, map_natCast, add_right_inj] at h3
    exact mul_left_cancel₀ (pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)) h3

end Unit

section Sep

variable {L Ω : Type} [Field L] [NumberField L] [Field Ω] [CharZero Ω] [Algebra L Ω] {l : ℕ} [Fact l.Prime]

theorem exists_sep [Normal ℚ L] {A : ValuationSubring Ω} {w : Plc L} (h : IsPlaceOver A w)
    (hl : ((l : ℕ) : 𝓞 L) ∈ w.asIdeal) (g : G ℚ Ω) (hg : g ∈ Dec (F := ℚ) A) (x : L)
    (hx : g (algebraMap L Ω x) ≠ algebraMap L Ω x) :
    ∃ (b : 𝓞 L) (τ₁ τ₂ : Emb l w), τ₁.1 (algebraMap L (w.adicCompletion L) (b : L)) ≠
      τ₂.1 (algebraMap L (w.adicCompletion L) (b : L)) := by
  obtain ⟨-, -, ⟨τ₀⟩, -, -⟩ := norm_data hl
  let g' : L ≃ₐ[ℚ] L := g.restrictNormal L
  have hg' : ∀ y : L, algebraMap L Ω (g' y) = g (algebraMap L Ω y) := fun y => g.restrictNormal_commutes L y
  obtain ⟨b, hb⟩ : ∃ b : 𝓞 L, g' (b : L) ≠ (b : L) := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨a, c, hc, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 L) (K := L) x
    apply hx
    have e1 : g' (algebraMap (𝓞 L) L a) = algebraMap (𝓞 L) L a := hcon a
    have e2 : g' (algebraMap (𝓞 L) L c) = algebraMap (𝓞 L) L c := hcon c
    rw [← hg', map_div₀, e1, e2]
  let c : L →+* Qbar l := (τ₀.1.comp (algebraMap L (w.adicCompletion L))).comp (g' : L →+* L)
  obtain ⟨u, hu⟩ := GlobalTheory.LadicPlace.exists_place_of_embedding L l c
  have huw : u = w := by
    refine HeightOneSpectrum.ext (Ideal.ext fun a => ?_)
    let a' : 𝓞 L := ⟨g' a, (RingOfIntegers.isIntegral_coe a).map g'⟩
    have e1 : ‖c a‖ < 1 ↔ a' ∈ w.asIdeal := emb_lt_iff τ₀ a'
    have e0 : a ∈ u.asIdeal ↔ u.valuation L (a : L) < 1 := (u.valuation_lt_one_iff_mem a).symm
    rw [e0, hu, e1, ← h a', ← h a]
    change A.valuation (algebraMap L Ω (g' a)) < 1 ↔ _
    rw [hg']
    exact valuation_apply_lt_one_iff hg _
  subst huw
  obtain ⟨j, hj, hjc⟩ := GlobalTheory.exists_continuous_extension_adicCompletion L l c u hu
  refine ⟨b, τ₀, ⟨j, hj⟩, fun e => hb ?_⟩
  have e2 : j (algebraMap L (u.adicCompletion L) (b : L)) = c (b : L) := DFunLike.congr_fun hjc _
  have e3 : τ₀.1 (algebraMap L (u.adicCompletion L) (b : L)) = c (b : L) := e.trans e2
  exact ((τ₀.1.comp (algebraMap L (u.adicCompletion L))).injective e3).symm

end Sep

end UpperTheory.V.J.Wu
