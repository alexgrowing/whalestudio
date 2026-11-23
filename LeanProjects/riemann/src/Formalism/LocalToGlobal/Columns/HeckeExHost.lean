import Mathlib
import Formalism.LocalToGlobal.Columns.HeckeEx
import Formalism.LocalToGlobal.Columns.CyclotomicIsCyclotomicExtension

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Col

namespace HeckeExHost

open Formalism.L2.Host Formalism.L2.Host.CharEx Formalism.L2.Col.HeckeEx Formalism.L2.DIV
open scoped Pointwise

section Gen

variable {X : Fields}

theorem unram_of (hX : X.AbelianUnramifiedExtensionConditions) (P : HeightOneSpectrum (𝓞 X.E)) : P.asIdeal.ramificationIdx (𝓞 X.F) = 1 := by
  have hne : P.asIdeal.under (𝓞 X.F) ≠ ⊥ := (P.under (𝓞 X.F)).ne_bot
  have := P.isPrime
  have : P.asIdeal.LiesOver (P.asIdeal.under (𝓞 X.F)) := ⟨rfl⟩
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx (P.asIdeal.under (𝓞 X.F)) P.asIdeal hne]
  apply Ideal.ramificationIdx'_spec
  · rw [pow_one]
    exact Ideal.map_comap_le
  · exact hX.unram P

theorem algebraMap_ne_imaginary (hX : X.Ok) {s0 : X.E} (hne : s0 ≠ 0) (hc : star s0 = -s0) (a : X.F) : algebraMap X.F X.E a ≠ s0 := by
  intro h
  have h1 := hX.star_F a
  rw [h, hc] at h1
  apply hne
  have h2 : s0 + s0 = 0 := by
    nth_rewrite 1 [← h1]
    exact neg_add_cancel s0
  exact add_self_eq_zero.mp h2

theorem li_pair (hX : X.Ok) {s0 : X.E} (hne : s0 ≠ 0) (hc : star s0 = -s0) : LinearIndependent X.F ![(1 : X.E), s0] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have ht : t = 0 := by
    by_contra ht
    apply algebraMap_ne_imaginary hX hne hc (-s / t)
    rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
    have htE : algebraMap X.F X.E t ≠ 0 := (map_ne_zero _).mpr ht
    rw [map_div₀, map_neg, div_eq_iff htE]
    linear_combination -hst
  subst ht
  refine ⟨?_, rfl⟩
  rw [zero_smul, add_zero, Algebra.smul_def, mul_one] at hst
  exact (map_eq_zero (algebraMap X.F X.E)).mp hst

theorem exists_pair (hX : X.Ok) {s0 : X.E} (hne : s0 ≠ 0) (hc : star s0 = -s0) (x : X.E) :
    ∃ a b : X.F, x = algebraMap X.F X.E a + algebraMap X.F X.E b * s0 := by
  have hli := li_pair hX hne hc
  have hcard : Fintype.card (Fin 2) = Module.finrank X.F X.E := by rw [hX.rankE]; rfl
  set b := basisOfLinearIndependentOfCardEqFinrank hli hcard with hb
  refine ⟨b.repr x 0, b.repr x 1, ?_⟩
  conv_lhs => rw [← b.sum_repr x]
  simp [hb, Fin.sum_univ_two, Algebra.smul_def]

theorem fixF_of (hX : X.Ok) {s0 : X.E} (hne : s0 ≠ 0) (hc : star s0 = -s0) (x : X.E) (hx : star x = x) :
    ∃ a : X.F, algebraMap X.F X.E a = x := by
  obtain ⟨a, b, rfl⟩ := exists_pair hX hne hc x
  refine ⟨a, ?_⟩
  have hb : algebraMap X.F X.E b * s0 = 0 := by
    rw [star_add, star_mul, hX.star_F, hX.star_F, hc] at hx
    have h2 : (2 : X.E) * (algebraMap X.F X.E b * s0) = 0 := by linear_combination -hx
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd h two_ne_zero
    · exact h
  rcases mul_eq_zero.mp hb with h | h
  · rw [h, zero_mul, add_zero]
  · exact absurd h hne

theorem conj_alg (hX : X.Ok) (φ : X.E →+* ℂ) (a : X.F) :
    starRingEnd ℂ (φ (algebraMap X.F X.E a)) = φ (algebraMap X.F X.E a) := by
  rw [← hX.conjE, hX.star_F]

open Classical in

theorem onePsi_of (hX : X.Ok) (σ₀ : X.K →+* ℂ) {s0 : X.E} (hne : s0 ≠ 0) (hc : star s0 = -s0)
    (hpos : ∀ i, ∃ r : ℝ, 0 < r ∧ X.embC σ₀ i s0 = Complex.I * r) (w : InfinitePlace X.F) :
    (Finset.univ.filter (fun i => InfinitePlace.mk (X.embC σ₀ i) ∈ aboveInf (L := X.E) X.F w)).card = 1 := by

  have hinj : Function.Injective (X.embC σ₀) := by
    intro τ τ' h
    apply hX.emb_inj
    ext x
    exact σ₀.injective (RingHom.congr_fun h x)
  let Φ : X.Tau ⊕ X.Tau → (X.E →+* ℂ) := Sum.elim (X.embC σ₀) fun τ => (starRingEnd ℂ).comp (X.embC σ₀ τ)
  have hΦ : Function.Injective Φ := by
    have hcs : ∀ τ τ', X.embC σ₀ τ ≠ (starRingEnd ℂ).comp (X.embC σ₀ τ') := by
      intro τ τ' h
      obtain ⟨r, hr, h1⟩ := hpos τ
      obtain ⟨r', hr', h2⟩ := hpos τ'
      have h3 := RingHom.congr_fun h s0
      rw [RingHom.comp_apply, h1, h2, map_mul, Complex.conj_I, Complex.conj_ofReal] at h3
      have h4 := congrArg Complex.im h3
      simp at h4
      linarith
    rintro (τ | τ) (τ' | τ') h
    · exact congrArg Sum.inl (hinj h)
    · exact absurd h (hcs τ τ')
    · exact absurd h.symm (hcs τ' τ)
    · congr 1
      apply hinj
      ext x
      have := RingHom.congr_fun h x
      simp only [Φ, Sum.elim_inr, RingHom.comp_apply] at this
      exact (starRingEnd ℂ).injective this
  have hcardE : Fintype.card (X.E →+* ℂ) = 2 * Fintype.card X.Tau := by
    rw [Embeddings.card, ← Module.finrank_mul_finrank ℚ X.F X.E, hX.rankE, hX.card_Tau, mul_comm]
  have hsurj : Function.Surjective Φ := by
    have hc2 : Fintype.card (X.Tau ⊕ X.Tau) = Fintype.card (X.E →+* ℂ) := by
      rw [Fintype.card_sum, hcardE]; ring
    exact ((Fintype.bijective_iff_injective_and_card Φ).2 ⟨hΦ, hc2⟩).2

  have hs2 : ∃ a : X.F, algebraMap X.F X.E a = s0 ^ 2 := fixF_of hX hne hc _ (by rw [star_pow, hc]; ring)
  have huniq : ∀ i τ, (InfinitePlace.mk (X.embC σ₀ i)).comap (algebraMap X.F X.E) =
      (InfinitePlace.mk (X.embC σ₀ τ)).comap (algebraMap X.F X.E) → i = τ := by
    intro i τ h
    have hagree : ∀ a : X.F, X.embC σ₀ i (algebraMap X.F X.E a) = X.embC σ₀ τ (algebraMap X.F X.E a) := by
      rw [InfinitePlace.comap_mk, InfinitePlace.comap_mk, InfinitePlace.mk_eq_iff] at h
      intro a
      rcases h with h | h
      · exact RingHom.congr_fun h a
      · have h1 := RingHom.congr_fun h a
        rw [ComplexEmbedding.conjugate_coe_eq] at h1
        change starRingEnd ℂ (X.embC σ₀ i (algebraMap X.F X.E a)) = _ at h1
        rw [conj_alg hX] at h1
        exact h1
    obtain ⟨r, hr, h1⟩ := hpos i
    obtain ⟨r', hr', h2⟩ := hpos τ
    obtain ⟨a2, ha2⟩ := hs2
    have hrr : r = r' := by
      have h3 := hagree a2
      rw [ha2, map_pow, map_pow, h1, h2] at h3
      have h4 : ((r : ℂ) ^ 2) = (r' : ℂ) ^ 2 := by
        have : (Complex.I * r) ^ 2 = -(r : ℂ) ^ 2 := by rw [mul_pow, Complex.I_sq]; ring
        have h' : (Complex.I * r') ^ 2 = -(r' : ℂ) ^ 2 := by rw [mul_pow, Complex.I_sq]; ring
        rw [this, h'] at h3
        linear_combination -h3
      have h5 : r ^ 2 = r' ^ 2 := by exact_mod_cast h4
      nlinarith [sq_nonneg (r - r'), sq_nonneg (r + r')]
    apply hinj
    ext x
    obtain ⟨a, b, rfl⟩ := exists_pair hX hne hc x
    rw [map_add, map_add, map_mul, map_mul, hagree a, hagree b, h1, h2, hrr]

  have : Algebra.IsAlgebraic X.F X.E := inferInstance
  obtain ⟨w', hw'⟩ := InfinitePlace.comap_surjective (k := X.F) (K := X.E) w
  obtain ⟨τ, hτ⟩ : ∃ τ, InfinitePlace.mk (X.embC σ₀ τ) = w' := by
    obtain ⟨t, ht⟩ := hsurj w'.embedding
    rcases t with τ | τ
    · exact ⟨τ, by rw [show X.embC σ₀ τ = w'.embedding from ht, InfinitePlace.mk_embedding]⟩
    · refine ⟨τ, ?_⟩
      have : (starRingEnd ℂ).comp (X.embC σ₀ τ) = w'.embedding := ht
      have h2 : (starRingEnd ℂ).comp (X.embC σ₀ τ) = ComplexEmbedding.conjugate (X.embC σ₀ τ) := by ext x; rfl
      rw [← InfinitePlace.mk_conjugate_eq, ← h2, this, InfinitePlace.mk_embedding]
  rw [Finset.card_eq_one]
  refine ⟨τ, Finset.eq_singleton_iff_unique_mem.2 ⟨?_, ?_⟩⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, aboveInf]
    rw [hτ]
    exact hw'
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, aboveInf] at hi
    exact huniq i τ (by rw [hi, hτ]; exact hw'.symm)

theorem conjO_conjO' (x : 𝓞 X.E) : X.conjO (X.conjO x) = x := by
  apply RingOfIntegers.ext
  show starRingEnd X.E (starRingEnd X.E (x : X.E)) = (x : X.E)
  simp

def conjPrime₂ (P : HeightOneSpectrum (𝓞 X.E)) : HeightOneSpectrum (𝓞 X.E) where
  asIdeal := P.asIdeal.comap X.conjO
  isPrime := Ideal.IsPrime.comap _
  ne_bot := by
    intro h
    apply P.ne_bot
    rw [eq_bot_iff]
    intro x hx
    have : X.conjO x ∈ P.asIdeal.comap X.conjO := by
      rw [Ideal.mem_comap, conjO_conjO']
      exact hx
    rw [h, Ideal.mem_bot] at this
    rw [Ideal.mem_bot]
    have := congrArg X.conjO this
    rwa [conjO_conjO', map_zero] at this

theorem conjO_alg (hX : X.Ok) (a : 𝓞 X.F) : X.conjO (algebraMap (𝓞 X.F) (𝓞 X.E) a) = algebraMap (𝓞 X.F) (𝓞 X.E) a := by
  apply RingOfIntegers.ext
  show starRingEnd X.E (algebraMap (𝓞 X.E) X.E (algebraMap (𝓞 X.F) (𝓞 X.E) a)) =
    algebraMap (𝓞 X.E) X.E (algebraMap (𝓞 X.F) (𝓞 X.E) a)
  rw [starRingEnd_apply, ← IsScalarTower.algebraMap_apply (𝓞 X.F) (𝓞 X.E) X.E,
    IsScalarTower.algebraMap_apply (𝓞 X.F) X.F X.E]
  exact hX.star_F _

theorem conjP_under (hX : X.Ok) (P : HeightOneSpectrum (𝓞 X.E)) : (conjPrime₂ P).under (𝓞 X.F) = P.under (𝓞 X.F) := by
  have key : (P.asIdeal.comap X.conjO).comap (algebraMap (𝓞 X.F) (𝓞 X.E)) =
      P.asIdeal.comap (algebraMap (𝓞 X.F) (𝓞 X.E)) := by
    rw [Ideal.comap_comap, show X.conjO.comp (algebraMap (𝓞 X.F) (𝓞 X.E)) = algebraMap (𝓞 X.F) (𝓞 X.E) from
      RingHom.ext fun a => conjO_alg hX a]
  ext1
  exact key

theorem mem_of_ordF (P : HeightOneSpectrum (𝓞 X.E)) (s : X.Eˣ) (y : 𝓞 X.E) (hy : (y : X.E) = s) (h : ordF P s ≠ 0) :
    y ∈ P.asIdeal := by
  by_contra hny
  apply h
  have h1 : P.intValuation y = 1 :=
    le_antisymm (P.intValuation_le_one y)
      (not_lt.mp fun hlt => hny ((P.intValuation_lt_one_iff_mem y).mp hlt))
  have h2 : P.valuation X.E (s : X.E) = 1 := by
    rw [← hy, show (y : X.E) = algebraMap (𝓞 X.E) X.E y from rfl,
      HeightOneSpectrum.valuation_of_algebraMap, h1]
  unfold Formalism.L2.Host.ordF
  rw [h2]
  simp

theorem dsplit_of (hX : X.Ok) {s0 : X.E} (y0 : 𝓞 X.E) (hy0 : (y0 : X.E) = s0)
    (hmove : ∀ P : HeightOneSpectrum (𝓞 X.E), y0 ∈ P.asIdeal → P.asIdeal.comap X.conjO ≠ P.asIdeal) :
    ∀ s : X.Eˣ, (s : X.E) = s0 → ∀ P : HeightOneSpectrum (𝓞 X.E), ordF P s ≠ 0 →
      (aboveF (L := X.E) X.F (P.under (𝓞 X.F))).card ≠ 1 := by
  intro s hs P hP hcard
  have hy : y0 ∈ P.asIdeal := mem_of_ordF P s y0 (hy0.trans hs.symm) hP
  have hne : conjPrime₂ P ≠ P := fun h => hmove P hy (congrArg HeightOneSpectrum.asIdeal h)
  obtain ⟨Q, hQ⟩ := Finset.card_eq_one.mp hcard
  have h1 : P ∈ aboveF (L := X.E) X.F (P.under (𝓞 X.F)) := by
    simp [Formalism.L2.Host.aboveF]
  have h2 : conjPrime₂ P ∈ aboveF (L := X.E) X.F (P.under (𝓞 X.F)) := by
    rw [← conjP_under hX P]
    simp [Formalism.L2.Host.aboveF]
  rw [hQ, Finset.mem_singleton] at h1 h2
  exact hne (h2.trans h1.symm)

end Gen

section Host

variable {R : Formalism.BasicNotions.Ranks} (H : Formalism.BasicNotions.Host R) (ι : Qb →+* ℂ) (LL : Fld) [FiniteDimensional ℚ LL] [Normal ℚ LL]
  (hE : H.EQ ≤ LL)

open Classical in

def sqrtH : (hostFields H.toHostRaw ι LL hE).E :=
  if ∃ τ, 0 < ((hostFields H.toHostRaw ι LL hE).embC (sig0 ι LL) τ (hwE H.toHostRaw ι LL hE)).im
  then hwE H.toHostRaw ι LL hE else -hwE H.toHostRaw ι LL hE

open Classical in

def sqrtHO : 𝓞 (hostFields H.toHostRaw ι LL hE).E :=
  if ∃ τ, 0 < ((hostFields H.toHostRaw ι LL hE).embC (sig0 ι LL) τ (hwE H.toHostRaw ι LL hE)).im
  then hwO H.toHostRaw ι LL hE else -hwO H.toHostRaw ι LL hE

theorem sqrtHO_coe : ((sqrtHO H ι LL hE : 𝓞 (hostFields H.toHostRaw ι LL hE).E) : (hostFields H.toHostRaw ι LL hE).E) =
    sqrtH H ι LL hE := by
  unfold sqrtHO sqrtH
  split_ifs
  · rfl
  · push_cast
    rfl

theorem sqrtH_star : star (sqrtH H ι LL hE) = -sqrtH H ι LL hE := by
  have hd : 0 < H.d := H.hyp.2.1.pos
  unfold sqrtH
  split_ifs
  · exact star_hwE H.toHostRaw ι LL hE hd
  · rw [star_neg, star_hwE H.toHostRaw ι LL hE hd, neg_neg]

theorem hwE_ne : hwE H.toHostRaw ι LL hE ≠ 0 := by
  intro h
  have h1 := hwE_sq H.toHostRaw ι LL hE
  rw [h, zero_pow two_ne_zero, zero_eq_neg] at h1
  have hd : (H.d : (hostFields H.toHostRaw ι LL hE).E) ≠ 0 := Nat.cast_ne_zero.2 H.hyp.2.1.ne_zero
  exact hd h1

theorem sqrtH_ne : sqrtH H ι LL hE ≠ 0 := by
  unfold sqrtH
  split_ifs
  · exact hwE_ne H ι LL hE
  · exact neg_ne_zero.mpr (hwE_ne H ι LL hE)

theorem sqrtH_pos (i : (hostFields H.toHostRaw ι LL hE).Tau) :
    ∃ r : ℝ, 0 < r ∧ (hostFields H.toHostRaw ι LL hE).embC (sig0 ι LL) i (sqrtH H ι LL hE) = Complex.I * r := by
  let v : (hostFields H.toHostRaw ι LL hE).Tau → ℂ := fun τ =>
    (hostFields H.toHostRaw ι LL hE).embC (sig0 ι LL) τ (hwE H.toHostRaw ι LL hE)
  have hd : (0 : ℝ) < Real.sqrt H.d := Real.sqrt_pos.2 (by exact_mod_cast H.hyp.2.1.pos)
  have hsq : ∀ τ, v τ ^ 2 = (Complex.I * (Real.sqrt H.d : ℂ)) ^ 2 := by
    intro τ
    have h1 : v τ ^ 2 = (hostFields H.toHostRaw ι LL hE).embC (sig0 ι LL) τ (hwE H.toHostRaw ι LL hE ^ 2) := by
      rw [map_pow]
    rw [h1, hwE_sq, map_neg, map_natCast, mul_pow, Complex.I_sq, ← Complex.ofReal_pow,
      Real.sq_sqrt (Nat.cast_nonneg _)]
    push_cast
    ring
  have hK : ∀ τ τ', v τ = v τ' := fun τ τ' => congrArg (sig0 ι LL) (hwE_Kq H.toHostRaw ι LL hE τ τ')
  have hpm : ∀ τ, v τ = Complex.I * (Real.sqrt H.d : ℂ) ∨ v τ = -(Complex.I * (Real.sqrt H.d : ℂ)) :=
    fun τ => sq_eq_sq_iff_eq_or_eq_neg.1 (hsq τ)
  have hIm : (Complex.I * (Real.sqrt H.d : ℂ)).im = Real.sqrt H.d := by simp
  refine ⟨Real.sqrt H.d, hd, ?_⟩
  unfold sqrtH
  split_ifs with h
  · obtain ⟨τ0, hτ0⟩ := h
    rcases hpm τ0 with h1 | h1
    · exact (hK i τ0).trans h1
    · exfalso
      have : (v τ0).im = -Real.sqrt H.d := by rw [h1, Complex.neg_im, hIm]
      have h2 : 0 < (v τ0).im := hτ0
      linarith
  · push Not at h
    rw [map_neg]
    rcases hpm i with h1 | h1
    · exfalso
      have h2 : (v i).im ≤ 0 := h i
      rw [h1, hIm] at h2
      linarith
    · have h3 : -(v i) = Complex.I * (Real.sqrt H.d : ℂ) := by rw [h1, neg_neg]
      exact h3

def toX (y : H.EQ) : (hostFields H.toHostRaw ι LL hE).E := y

theorem frame_conj (T : Frame H) (x : H.E) :
    toX H ι LL hE (T.iso (H.conj x)) = star (toX H ι LL hE (T.iso x)) := by
  let φ : (hostFields H.toHostRaw ι LL hE).E →+* ℂ :=
    (T.ι.comp T.j.toRingHom).comp (T.iso.symm : H.EQ ≃ₐ[ℚ] H.E).toRingEquiv.toRingHom
  have hφ : ∀ y : H.E, φ (toX H ι LL hE (T.iso y)) = T.ι (T.j y) := by
    intro y
    show T.ι (T.j (T.iso.symm (T.iso y))) = _
    rw [AlgEquiv.symm_apply_apply]
  apply φ.injective
  rw [(hostFields_ok H ι LL hE).conjE φ, hφ, hφ, T.conj]

theorem roots_host (hmu : H.toHostRaw.MuPM) (z : (hostFields H.toHostRaw ι LL hE).E) (hz : ∃ n : ℕ, 0 < n ∧ z ^ n = 1) :
    z = 1 ∨ z = -1 := by
  obtain ⟨T⟩ := Frame.exists H
  obtain ⟨n, hn, hzn⟩ := hz
  let z' : H.EQ := z
  have hz' : z' ^ n = 1 := hzn
  have h := hmu (T.iso.symm z') ⟨n, hn, by rw [← map_pow, hz', map_one]⟩
  have h2 : z' = 1 ∨ z' = -1 := by
    rcases h with h | h
    · left
      rw [← T.iso.apply_symm_apply z', h, map_one]
    · right
      rw [← T.iso.apply_symm_apply z', h, map_neg, map_one]
  exact h2

theorem move_host (P : HeightOneSpectrum (𝓞 (hostFields H.toHostRaw ι LL hE).E)) (hP : sqrtHO H ι LL hE ∈ P.asIdeal) :
    P.asIdeal.comap (hostFields H.toHostRaw ι LL hE).conjO ≠ P.asIdeal := by
  intro hfix
  obtain ⟨T⟩ := Frame.exists H
  have hw : hwO H.toHostRaw ι LL hE ∈ P.asIdeal := by
    unfold sqrtHO at hP
    split_ifs at hP
    · exact hP
    · exact (P.asIdeal.neg_mem_iff).1 hP
  have hdP : ((H.d : ℤ) : 𝓞 (hostFields H.toHostRaw ι LL hE).E) ∈ P.asIdeal := by
    have h2 : hwO H.toHostRaw ι LL hE ^ 2 ∈ P.asIdeal := Ideal.pow_mem_of_mem _ hw 2 two_pos
    rw [hwO_sq] at h2
    have := (P.asIdeal.neg_mem_iff).1 h2
    simpa using this
  let eO : 𝓞 H.E ≃+* 𝓞 (hostFields H.toHostRaw ι LL hE).E :=
    RingOfIntegers.mapRingEquiv (T.iso : H.E ≃ₐ[ℚ] H.EQ).toRingEquiv
  have hdP' : ((H.d : ℤ) : 𝓞 H.E) ∈ P.asIdeal.comap (eO : 𝓞 H.E →+* 𝓞 (hostFields H.toHostRaw ι LL hE).E) := by
    rw [Ideal.mem_comap, map_intCast]
    exact hdP
  let P' : HeightOneSpectrum (𝓞 H.E) :=
    { asIdeal := P.asIdeal.comap (eO : 𝓞 H.E →+* 𝓞 (hostFields H.toHostRaw ι LL hE).E)
      isPrime := Ideal.IsPrime.comap _
      ne_bot := by
        intro h
        rw [h, Ideal.mem_bot] at hdP'
        have hd0 : ((H.d : ℤ) : 𝓞 H.E) ≠ 0 := by exact_mod_cast H.hyp.2.1.ne_zero
        exact hd0 hdP' }
  have := P'.isPrime
  have := PI.UnitaryGroupMassFormula.HostPrimeFacts.liesOver_d H P' hdP'
  apply H.der.decompConj H.d H.hyp.2.1 (Dvd.intro_left _ rfl) P'.asIdeal
  rw [MulAction.mem_stabilizer_iff]
  ext z
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
  have key : eO (H.conj⁻¹ • z) = (hostFields H.toHostRaw ι LL hE).conjO (eO z) := by
    apply RingOfIntegers.ext
    show toX H ι LL hE (T.iso (H.conj⁻¹ (z : H.E))) = star (toX H ι LL hE (T.iso (z : H.E)))
    have h1 := frame_conj H ι LL hE T (H.conj⁻¹ (z : H.E))
    rw [show H.conj (H.conj⁻¹ (z : H.E)) = (z : H.E) from AlgEquiv.apply_symm_apply _ _] at h1
    rw [h1, star_star]
  show eO (H.conj⁻¹ • z) ∈ P.asIdeal ↔ eO z ∈ P.asIdeal
  rw [key, ← Ideal.mem_comap, hfix]

theorem etaFactsC_host (hmu : H.toHostRaw.MuPM) :
    EtaFactsC (hostFields H.toHostRaw ι LL hE) (sig0 ι LL) (sqrtH H ι LL hE) where
  unram P _ := unram_of (base_fields_conditions H ι LL hE) P
  onePsi w := onePsi_of (hostFields_ok H ι LL hE) (sig0 ι LL) (sqrtH_ne H ι LL hE) (sqrtH_star H ι LL hE)
    (sqrtH_pos H ι LL hE) w
  fixF := fixF_of (hostFields_ok H ι LL hE) (sqrtH_ne H ι LL hE) (sqrtH_star H ι LL hE)
  roots := roots_host H ι LL hE hmu
  sqrt_ne := sqrtH_ne H ι LL hE
  isCMField_complexConj_s_eq_neg := sqrtH_star H ι LL hE
  sqrt_pos s hs i := by rw [hs]; exact sqrtH_pos H ι LL hE i
  card4 := (base_fields_conditions H ι LL hE).four_dvd_f
  dsplit := dsplit_of (hostFields_ok H ι LL hE) (sqrtHO H ι LL hE) (sqrtHO_coe H ι LL hE) (move_host H ι LL hE)

theorem exists_etaFactsC_host (hmu : H.toHostRaw.MuPM) :
    ∃ s0, EtaFactsC (hostFields H.toHostRaw ι LL hE) (sig0 ι LL) s0 := ⟨_, etaFactsC_host H ι LL hE hmu⟩

end Host

end HeckeExHost

end Formalism.L2.Col
