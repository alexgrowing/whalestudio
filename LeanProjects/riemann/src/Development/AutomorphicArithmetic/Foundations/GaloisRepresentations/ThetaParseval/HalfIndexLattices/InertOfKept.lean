import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.LatRepB_A
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentCoprimeAtGoodPlaces

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open PositivityTheory.ThKW.AutEtaA

namespace UpperTheory.TP.W

section FF

variable {k : Type} [Field k] [Finite k] {q : ℕ} [Fact q.Prime] [CharP k q]

private theorem two_ne (hq : q ≠ 2) : (2 : k) ≠ 0 := by
  intro h
  have h1 : ((2 : ℕ) : k) = 0 := by exact_mod_cast h
  have h2 := (CharP.cast_eq_zero_iff k q 2).1 h1
  exact hq ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 h2)

private theorem pow_q_eq (hq : q ≠ 2) {s a : ℤ} (hs : (a : ZMod q) ^ (q / 2) = (s : ZMod q)) {y : k}
    (hy : y ^ 2 = (a : k)) : y ^ q = (s : k) * y := by
  have hodd : q = 2 * (q / 2) + 1 := by
    have := (Fact.out : q.Prime).eq_two_or_odd
    omega
  have h1 : (a : k) ^ (q / 2) = (s : k) := by
    have := congrArg (ZMod.castHom (dvd_refl q) k) hs
    simpa using this
  calc y ^ q = y ^ (2 * (q / 2) + 1) := by rw [← hodd]
    _ = (y ^ 2) ^ (q / 2) * y := by rw [pow_succ, pow_mul]
    _ = (s : k) * y := by rw [hy, h1]

private theorem pow_q_pow (hq : q ≠ 2) {s a : ℤ} (hs : (a : ZMod q) ^ (q / 2) = (s : ZMod q))
    (hs1 : s = 1 ∨ s = -1) {y : k} (hy : y ^ 2 = (a : k)) (j : ℕ) : y ^ (q ^ j) = (s : k) ^ j * y := by
  have hodd : Odd q := (Fact.out : q.Prime).odd_of_ne_two hq
  have hsq : (s : k) ^ q = (s : k) := by
    rcases hs1 with rfl | rfl
    · simp
    · simpa using hodd.neg_one_pow (α := k)
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, pow_mul, ih, mul_pow, pow_q_eq hq hs hy, ← pow_mul, mul_comm j q, pow_mul, hsq, pow_succ]
    ring

private theorem even_of_neg (hq : q ≠ 2) {a : ℤ} (hs : (a : ZMod q) ^ (q / 2) = ((-1 : ℤ) : ZMod q))
    {y : k} (hy : y ^ 2 = (a : k)) (hy0 : y ≠ 0) {m : ℕ} (hc : Nat.card k = q ^ m) : Even m := by
  haveI := Fintype.ofFinite k
  have h1 := pow_q_pow hq hs (Or.inr rfl) hy m
  rw [← hc, Nat.card_eq_fintype_card, FiniteField.pow_card] at h1
  by_contra hm
  rw [Nat.not_even_iff_odd] at hm
  have h2 : (((-1 : ℤ) : k)) ^ m = -1 := by simpa using hm.neg_one_pow (α := k)
  rw [h2] at h1
  have h3 : (2 : k) * y = 0 := by linear_combination h1
  exact (mul_ne_zero (two_ne hq) hy0) h3

private theorem invol_data (hq : q ≠ 2) {s a : ℤ} (hs : (a : ZMod q) ^ (q / 2) = (s : ZMod q))
    (hs1 : s = 1 ∨ s = -1) {y : k} (hy : y ^ 2 = (a : k)) (hy0 : y ≠ 0) (τ : k →+* k)
    (hτ : ∀ z, τ (τ z) = z) (hτy : τ y = -y) {m : ℕ} (hc : Nat.card k = q ^ m) :
    s = -1 ∧ ∃ j, Odd j ∧ m = 2 * j := by
  letI : Algebra (ZMod q) k := ZMod.algebra k q
  let σ : k ≃ₐ[ZMod q] k := AlgEquiv.ofRingEquiv (f := RingEquiv.ofRingHom τ τ (RingHom.ext hτ) (RingHom.ext hτ))
    (fun x => by
      obtain ⟨n, rfl⟩ := ZMod.natCast_zmod_surjective x
      simp)
  have hσ : ∀ z, σ z = τ z := fun _ => rfl
  obtain ⟨⟨j, hj⟩, e⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow (ZMod q) k).2 σ
  have ho := FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic (ZMod q) k
  simp only at e
  have h3 : ∀ z, σ z = z ^ (q ^ j) := fun z => by
    have h4 : σ z = (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod q) k ^ j) z := by rw [e]
    rw [AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate, ZMod.card] at h4
    exact h4
  have h2 : FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod q) k ^ (2 * j) = 1 := by
    rw [mul_comm, pow_mul, e]
    ext x
    exact hτ x
  have hdvd := orderOf_dvd_of_pow_eq_one h2
  rw [ho] at hdvd
  have hyy : (s : k) ^ j * y = -y := by
    rw [← pow_q_pow hq hs hs1 hy j, ← h3, hσ, hτy]
  have hsj : (s : k) ^ j = -1 := by
    have : ((s : k) ^ j + 1) * y = 0 := by linear_combination hyy
    have h5 := (mul_eq_zero.1 this).resolve_right hy0
    linear_combination h5
  have h21 : (1 : k) ≠ -1 := fun h => two_ne (k := k) hq (by linear_combination h)
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact h21 (by simpa using hsj)
  have hn : Module.finrank (ZMod q) k = 2 * j := by
    obtain ⟨c, hc'⟩ := hdvd
    have : c = 1 := by
      rcases c with _ | _ | c
      · omega
      · rfl
      · nlinarith
    rw [hc', this, mul_one]
  have hcard : Nat.card k = q ^ (2 * j) := by
    rw [← hn, Module.natCard_eq_pow_finrank (K := ZMod q), Nat.card_zmod]
  have hm : m = 2 * j := by
    rw [hc] at hcard
    exact Nat.pow_right_injective (Fact.out : q.Prime).two_le hcard
  rcases hs1 with rfl | rfl
  · exfalso
    apply h21
    simpa using hsj
  · refine ⟨rfl, j, ?_, hm⟩
    by_contra hodd
    rw [Nat.not_odd_iff_even] at hodd
    have h6 := hodd.neg_one_pow (α := k)
    have h7 : ((-1 : ℤ) : k) = -1 := by simp
    rw [h7, h6] at hsj
    exact h21 hsj

end FF

section Arith

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

private theorem sg_neg (h : IsCMExt F E σ) {y : 𝓞 E} {a : ℕ} (ha : 0 < a) (hy : y ^ 2 = -(a : 𝓞 E)) :
    sgOF σ y = -y := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply RingOfIntegers.ext
  apply τ.injective
  have h1 : (τ (y : E)) ^ 2 = -(a : ℂ) := by
    have := congrArg (fun t : 𝓞 E => τ (t : E)) hy
    simpa using this
  show τ (σ (y : E)) = τ (((-y : 𝓞 E)) : E)
  rw [h.2.2.2]
  have e : τ (((-y : 𝓞 E)) : E) = -τ (y : E) := by simp
  rw [e]
  generalize τ (y : E) = z at h1
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have him := congrArg Complex.im h1
  have hre := congrArg Complex.re h1
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.natCast_re,
    Complex.natCast_im, neg_zero] at him hre
  have hz : z.re = 0 := by
    by_contra hz
    have h0 : z.im = 0 := by
      have : z.re * z.im = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_left hz
    rw [h0] at hre
    nlinarith [mul_self_nonneg z.re]
  apply Complex.ext <;> simp [hz]

private theorem norm_mem (h : IsCMExt F E σ) (x : 𝓞 E) :
    ∃ c : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) c = x * sgOF σ x := by
  have hz : σ ((x : E) * σ x) = (x : E) * σ x := by
    rw [map_mul, GlobalTheory.SplitDetCharF.sig_invol h, mul_comm]
  have ht := PositivityTheory.ThKG.Tow.Pln.trace_cm h ((x : E) * σ x)
  rw [hz] at ht
  have e : algebraMap F E (Algebra.trace F E ((x : E) * σ x) / 2) = (x : E) * σ x := by
    rw [map_div₀, ht, map_ofNat]
    ring
  have hint : IsIntegral ℤ (Algebra.trace F E ((x : E) * σ x) / 2) := by
    rw [← isIntegral_algebraMap_iff (algebraMap F E).injective, e]
    exact RingOfIntegers.isIntegral_coe (x * sgOF σ x)
  exact ⟨⟨_, hint⟩, RingOfIntegers.ext e⟩

private theorem not_le_sq {A : Type} [CommRing A] [Algebra A (𝓞 E)] [Algebra.EssFiniteType A (𝓞 E)]
    (w : HeightOneSpectrum (𝓞 E)) (hu : Algebra.IsUnramifiedAt A w.asIdeal) :
    ¬ (w.asIdeal.under A).map (algebraMap A (𝓞 E)) ≤ w.asIdeal ^ 2 := by
  haveI := w.isPrime
  have hle : (w.asIdeal.under A).map (algebraMap A (𝓞 E)) ≤ w.asIdeal := Ideal.map_comap_le
  have h1 : Ideal.ramificationIdx' (w.asIdeal.under A) w.asIdeal = 1 := by
    letI := Localization.AtPrime.algebraOfLiesOver (w.asIdeal.under A) w.asIdeal
    exact (Ideal.IsDedekindDomain.ramificationIdx'_eq_one_iff w.ne_bot hle).2
      ((Algebra.isUnramifiedAt_iff_map_eq A (w.asIdeal.under A) w.asIdeal).1 hu).2
  exact fun h => (Ideal.ramificationIdx_ne_one_iff hle).2 h h1

private theorem inert_of_kept (h : IsCMExt F E σ) (hu : Algebra.Unramified (𝓞 F) (𝓞 E))
    (w : HeightOneSpectrum (𝓞 E)) (hk : Fx σ w) : Formalism.UG.IsInertAt F E (w.under (𝓞 F)) w := by
  classical
  haveI := w.isPrime
  set v := w.under (𝓞 F) with hv
  have hva : v.asIdeal = w.asIdeal.under (𝓞 F) := rfl
  have hinj : Function.Injective (algebraMap (𝓞 F) (𝓞 E)) := FaithfulSMul.algebraMap_injective _ _
  unfold Formalism.UG.IsInertAt
  have hle : v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E)) ≤ w.asIdeal := Ideal.map_comap_le
  have h2 : ¬ v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E)) ≤ w.asIdeal ^ 2 := not_le_sq w inferInstance
  set I := Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal with hI
  have hI0 : I ≠ ⊥ := by
    rw [hI, Ne, Ideal.map_eq_bot_iff_of_injective hinj]
    exact v.ne_bot
  have hfac : ∀ p ∈ UniqueFactorizationMonoid.normalizedFactors I, p = w.asIdeal := by
    intro p hp
    obtain ⟨hpp, hpl⟩ := (Ideal.mem_normalizedFactors_iff hI0).1 hp
    have hp0 : p ≠ ⊥ := fun h0 => hI0 (le_bot_iff.1 (h0 ▸ hpl))
    have hcp : p.comap (algebraMap (𝓞 F) (𝓞 E)) = v.asIdeal :=
      (v.isMaximal.eq_of_le (Ideal.comap_ne_top _ hpp.ne_top) (Ideal.map_le_iff_le_comap.1 hpl)).symm
    refine (hpp.isMaximal hp0).eq_of_le w.isPrime.ne_top fun x hx => ?_
    obtain ⟨c, hc⟩ := norm_mem h x
    have h3 : c ∈ p.comap (algebraMap (𝓞 F) (𝓞 E)) := by
      rw [Ideal.mem_comap, hc]
      exact p.mul_mem_right _ hx
    rw [hcp, hva, Ideal.under, Ideal.mem_comap, hc] at h3
    rcases w.isPrime.mem_or_mem h3 with h4 | h4
    · exact h4
    · have := hk _ h4
      rwa [sgOF_sgOF h] at this
  obtain ⟨n, hn⟩ : ∃ n, I = w.asIdeal ^ n := by
    refine ⟨Multiset.card (UniqueFactorizationMonoid.normalizedFactors I), ?_⟩
    conv_lhs => rw [← Ideal.prod_normalizedFactors_eq_self hI0]
    rw [Multiset.eq_replicate_card.2 hfac, Multiset.prod_replicate, Multiset.card_replicate]
  rcases n with _ | _ | n
  · exfalso
    rw [hn, pow_zero, Ideal.one_eq_top, top_le_iff] at hle
    exact w.isPrime.ne_top hle
  · simpa using hn
  · exfalso
    exact h2 (hn.le.trans (Ideal.pow_le_pow_right (by omega)))

private theorem unram_int {B : Base F E} (hG : GoodK σ B) (w : HeightOneSpectrum (𝓞 E)) (hk : Fx σ w) :
    (2 : 𝓞 F) ∉ (w.under (𝓞 F)).asIdeal ∧ Algebra.IsUnramifiedAt ℤ w.asIdeal := by
  haveI := hG.unram
  haveI := w.isPrime
  have hin := hG.inert _ w (inert_of_kept hG.cm hG.unram w hk)
  refine ⟨hin.1, ?_⟩
  have hnF := GlobalTheory.DiffCoprimeP.not_le_differentIdeal_of_psiUnr hG.std _ hin.2.2
  have hfu : Algebra.FormallyUnramified (𝓞 F) (𝓞 E) := inferInstance
  have hEq : differentIdeal ℤ (𝓞 E) = (differentIdeal ℤ (𝓞 F)).map (algebraMap (𝓞 F) (𝓞 E)) := by
    rw [differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 F) (𝓞 E),
      (GlobalTheory.formallyUnramified_ringOfIntegers_iff_differentIdeal_eq_top F E).1 hfu, Ideal.top_mul]
  refine not_dvd_differentIdeal_iff.1 fun hd => hnF ?_
  rw [Ideal.dvd_iff_le, hEq, Ideal.map_le_iff_le_comap] at hd
  exact hd

private theorem not_mem_sq (w : HeightOneSpectrum (𝓞 E)) (hu : Algebra.IsUnramifiedAt ℤ w.asIdeal) {q : ℕ}
    (hq : q.Prime) (hqw : (q : 𝓞 E) ∈ w.asIdeal) : (q : 𝓞 E) ∉ w.asIdeal ^ 2 := by
  intro hmem
  haveI := w.isPrime
  apply not_le_sq (A := ℤ) w hu
  have hmax : (Ideal.span {(q : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.1 hq).irreducible
  have hu' : w.asIdeal.under ℤ = Ideal.span {(q : ℤ)} :=
    (hmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance) (by
      rw [Ideal.span_singleton_le_iff_mem, Ideal.under, Ideal.mem_comap]
      simpa using hqw)).symm
  rw [hu', Ideal.map_span, Set.image_singleton, Ideal.span_singleton_le_iff_mem]
  simpa using hmem

private theorem not_dvd_of {a : ℕ} (hsq : Squarefree a) {y : 𝓞 E} (hy : y ^ 2 = -(a : 𝓞 E))
    (w : HeightOneSpectrum (𝓞 E)) {q : ℕ} (hq : q.Prime) (hqw : (q : 𝓞 E) ∈ w.asIdeal)
    (hn : (q : 𝓞 E) ∉ w.asIdeal ^ 2) : ¬ q ∣ a := by
  rintro ⟨c, rfl⟩
  have hc : ¬ q ∣ c := fun ⟨e, he⟩ => hq.not_isUnit (hsq q ⟨e, by rw [he]; ring⟩)
  have hcop := (Nat.Prime.coprime_iff_not_dvd hq).2 hc
  obtain ⟨u, t, hut⟩ := Nat.isCoprime_iff_coprime.2 hcop
  have hyw : y ∈ w.asIdeal := by
    have : y ^ 2 ∈ w.asIdeal := by
      rw [hy, Nat.cast_mul]
      exact neg_mem (w.asIdeal.mul_mem_right _ hqw)
    exact w.isPrime.mem_of_pow_mem 2 this
  have h1 : (u : 𝓞 E) * q + t * c = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 E) hut
  have h2 : (q : 𝓞 E) = (u : 𝓞 E) * (q * q) - t * y ^ 2 := by
    rw [hy]
    push_cast
    linear_combination (-(q : 𝓞 E)) * h1
  apply hn
  rw [h2, pow_two]
  refine sub_mem (Ideal.mul_mem_left _ _ (Ideal.mul_mem_mul hqw hqw)) (Ideal.mul_mem_left _ _ ?_)
  rw [pow_two]
  exact Ideal.mul_mem_mul hyw hyw

private theorem charP_res (P : Ideal (𝓞 E)) [hP : P.IsMaximal] [Finite (𝓞 E ⧸ P)] {q : ℕ} (hq : q.Prime)
    (hqP : (q : 𝓞 E) ∈ P) : letI := Ideal.Quotient.field P; CharP (𝓞 E ⧸ P) q := by
  letI := Ideal.Quotient.field P
  obtain ⟨p, hp⟩ := CharP.exists (𝓞 E ⧸ P)
  have hpp := CharP.char_is_prime (𝓞 E ⧸ P) p
  have h0 : ((q : ℕ) : 𝓞 E ⧸ P) = 0 := by
    have := Ideal.Quotient.eq_zero_iff_mem.2 hqP
    simpa using this
  have h1 := (CharP.cast_eq_zero_iff _ p q).1 h0
  have h2 := (Nat.prime_dvd_prime_iff_eq hpp hq).1 h1
  exact h2 ▸ hp

private theorem res_card (P : Ideal (𝓞 E)) [hP : P.IsMaximal] [Finite (𝓞 E ⧸ P)] {q : ℕ} (hq : q.Prime)
    (hqP : (q : 𝓞 E) ∈ P) : ∃ m, Nat.card (𝓞 E ⧸ P) = q ^ m := by
  letI := Ideal.Quotient.field P
  haveI := charP_res P hq hqP
  haveI := Fintype.ofFinite (𝓞 E ⧸ P)
  obtain ⟨n, -, hn⟩ := FiniteField.card (𝓞 E ⧸ P) q
  exact ⟨n, by rw [Nat.card_eq_fintype_card, hn]⟩

private theorem res_prime (P : Ideal (𝓞 E)) [hP : P.IsMaximal] [Finite (𝓞 E ⧸ P)] :
    ∃ q : ℕ, q.Prime ∧ (q : 𝓞 E) ∈ P := by
  letI := Ideal.Quotient.field P
  obtain ⟨p, hp⟩ := CharP.exists (𝓞 E ⧸ P)
  refine ⟨p, CharP.char_is_prime (𝓞 E ⧸ P) p, Ideal.Quotient.eq_zero_iff_mem.1 ?_⟩
  simpa using CharP.cast_eq_zero (𝓞 E ⧸ P) p

private theorem res_root {a : ℕ} {y : 𝓞 E} (hy : y ^ 2 = -(a : 𝓞 E)) (P : Ideal (𝓞 E)) [hP : P.IsMaximal]
    [Finite (𝓞 E ⧸ P)] {q : ℕ} (hq : q.Prime) (hqP : (q : 𝓞 E) ∈ P) (hnd : ¬ q ∣ a) :
    letI := Ideal.Quotient.field P
    (Ideal.Quotient.mk P y) ^ 2 = ((-(a : ℤ) : ℤ) : 𝓞 E ⧸ P) ∧ Ideal.Quotient.mk P y ≠ 0 := by
  letI := Ideal.Quotient.field P
  haveI := charP_res P hq hqP
  have h1 : (Ideal.Quotient.mk P y) ^ 2 = ((-(a : ℤ) : ℤ) : 𝓞 E ⧸ P) := by
    have := congrArg (Ideal.Quotient.mk P) hy
    simpa using this
  refine ⟨h1, fun h0 => hnd ?_⟩
  rw [h0] at h1
  have h2 : ((a : ℕ) : 𝓞 E ⧸ P) = 0 := by
    have : ((a : ℕ) : 𝓞 E ⧸ P) = -((-(a : ℤ) : ℤ) : 𝓞 E ⧸ P) := by simp
    rw [this, ← h1]
    simp
  exact (CharP.cast_eq_zero_iff _ q a).1 h2

private theorem kept_deg {B : Base F E} (hG : GoodK σ B) {a : ℕ} (hsq : Squarefree a) {y : 𝓞 E}
    (hs' : sgOF σ y = -y) (hy : y ^ 2 = -(a : 𝓞 E)) (P : Ideal (𝓞 E)) [hP : P.IsMaximal]
    [Finite (𝓞 E ⧸ P)] {q m : ℕ} (hq : q.Prime) (hqP : (q : 𝓞 E) ∈ P) (hc : Nat.card (𝓞 E ⧸ P) = q ^ m)
    (hk : ∀ r ∈ P, sgOF σ r ∈ P) :
    q ≠ 2 ∧ ¬ q ∣ a ∧ ((-(a : ℤ) : ℤ) : ZMod q) ^ (q / 2) = ((-1 : ℤ) : ZMod q) ∧ ∃ j, Odd j ∧ m = 2 * j := by
  have hP0 : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField _)
  let w : HeightOneSpectrum (𝓞 E) := ⟨P, hP.isPrime, hP0⟩
  obtain ⟨h2F, hu⟩ := unram_int hG w hk
  have h2 : q ≠ 2 := by
    rintro rfl
    apply h2F
    show (2 : 𝓞 F) ∈ P.comap (algebraMap (𝓞 F) (𝓞 E))
    rw [Ideal.mem_comap, map_ofNat]
    simpa using hqP
  have hnd := not_dvd_of hsq hy w hq hqP (not_mem_sq w hu hq hqP)
  haveI : Fact q.Prime := ⟨hq⟩
  letI := Ideal.Quotient.field P
  haveI := charP_res P hq hqP
  have ha0 : ((-(a : ℤ) : ℤ) : ZMod q) ≠ 0 := by
    intro h
    apply hnd
    have : ((a : ℕ) : ZMod q) = 0 := by simpa using h
    exact (ZMod.natCast_eq_zero_iff a q).1 this
  obtain ⟨s, hs1, hs⟩ : ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ ((-(a : ℤ) : ℤ) : ZMod q) ^ (q / 2) = (s : ZMod q) := by
    rcases ZMod.pow_div_two_eq_neg_one_or_one q ha0 with h | h
    · exact ⟨1, Or.inl rfl, by simpa using h⟩
    · exact ⟨-1, Or.inr rfl, by simpa using h⟩
  obtain ⟨hyb, hy0⟩ := res_root hy P hq hqP hnd
  let τ : (𝓞 E ⧸ P) →+* (𝓞 E ⧸ P) := Ideal.quotientMap P (sgOF σ) (fun r hr => hk r hr)
  have hτm : ∀ r, τ (Ideal.Quotient.mk P r) = Ideal.Quotient.mk P (sgOF σ r) := fun r => Ideal.quotientMap_mk
  have hτ : ∀ z, τ (τ z) = z := fun z => by
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [hτm, hτm, sgOF_sgOF hG.cm]
  have hτy : τ (Ideal.Quotient.mk P y) = -Ideal.Quotient.mk P y := by
    rw [hτm, hs', map_neg]
  obtain ⟨rfl, hj⟩ := invol_data h2 hs hs1 hyb hy0 τ hτ hτy hc
  exact ⟨h2, hnd, hs, hj⟩

private theorem even_deg {a : ℕ} {y : 𝓞 E} (hy : y ^ 2 = -(a : 𝓞 E)) (P : Ideal (𝓞 E)) [hP : P.IsMaximal]
    [Finite (𝓞 E ⧸ P)] {q m : ℕ} (hq : q.Prime) (hqP : (q : 𝓞 E) ∈ P) (hc : Nat.card (𝓞 E ⧸ P) = q ^ m)
    (h2 : q ≠ 2) (hnd : ¬ q ∣ a) (hs : ((-(a : ℤ) : ℤ) : ZMod q) ^ (q / 2) = ((-1 : ℤ) : ZMod q)) : Even m := by
  haveI : Fact q.Prime := ⟨hq⟩
  letI := Ideal.Quotient.field P
  haveI := charP_res P hq hqP
  obtain ⟨hyb, hy0⟩ := res_root hy P hq hqP hnd
  exact even_of_neg h2 hs hyb hy0 hc

end Arith

theorem normK : NormK := by
  intro F E _ _ _ _ _ σ B hG
  classical
  obtain ⟨x, d, hd, hx⟩ := hG.galois
  obtain ⟨a, b, ha, hb, hab, hsq⟩ := Nat.sq_mul_squarefree_of_pos hd
  have hbE : (b : E) ≠ 0 := by exact_mod_cast hb.ne'
  have hz : (x / b) ^ 2 = -(a : E) := by
    rw [div_pow, hx, ← hab]
    push_cast
    field_simp
  have hint : IsIntegral ℤ (x / b) := by
    refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
    have : -(a : E) = algebraMap ℤ E (-(a : ℤ)) := by simp
    rw [hz, this]
    exact isIntegral_algebraMap
  obtain ⟨y, hye⟩ : ∃ y : 𝓞 E, (y : E) = x / b := ⟨⟨x / b, hint⟩, rfl⟩
  have hy : y ^ 2 = -(a : 𝓞 E) := RingOfIntegers.ext (by simpa [hye] using hz)
  have hs' : sgOF σ y = -y := sg_neg hG.cm ha hy
  let S : ℕ → Prop := fun q => ∃ P : Ideal (𝓞 E), P.IsMaximal ∧ Finite (𝓞 E ⧸ P) ∧ (q : 𝓞 E) ∈ P ∧
    ∀ r ∈ P, sgOF σ r ∈ P
  let u : ℕ → ℂ := fun q => (Real.sqrt q : ℂ) * if S q then Complex.I else 1
  have hne : ∀ n, n ≠ 0 → ofPrimeValues u n ≠ 0 := fun n => by
    induction n using Nat.recOnMul with
    | zero => simp
    | one => simp
    | prime q hq =>
      intro _
      rw [ofPrimeValues_prime u hq]
      refine mul_ne_zero ?_ ?_
      · exact_mod_cast (Real.sqrt_pos.2 (by exact_mod_cast hq.pos)).ne'
      · split_ifs
        · exact Complex.I_ne_zero
        · exact one_ne_zero
    | mul a b ha hb =>
      intro h
      rw [map_mul]
      exact mul_ne_zero (ha (left_ne_zero_of_mul h)) (hb (right_ne_zero_of_mul h))
  have hsqr : ∀ n : ℕ, ((Real.sqrt n : ℝ) : ℂ) ^ 2 = n := fun n => by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _), Complex.ofReal_natCast]
  refine ⟨ofPrimeValues u, hne, fun P hP hfin => ?_⟩
  obtain ⟨q, hq, hqP⟩ := res_prime P
  obtain ⟨m, hc⟩ := res_card P hq hqP
  have hl : ofPrimeValues u (q ^ m) = u q ^ m := by rw [map_pow, ofPrimeValues_prime u hq]
  by_cases hS : S q
  · have hu2 : u q ^ 2 = -(q : ℂ) := by
      simp only [u, if_pos hS, mul_pow, hsqr, Complex.I_sq]
      ring
    obtain ⟨P₀, hP₀, hf₀, hq₀, hk₀⟩ := hS
    obtain ⟨m₀, hc₀⟩ := res_card P₀ hq hq₀
    obtain ⟨h2, hnd, hs, -⟩ := kept_deg hG hsq hs' hy P₀ hq hq₀ hc₀ hk₀
    have hev := even_deg hy P hq hqP hc h2 hnd hs
    refine ⟨?_, fun hk => ⟨?_, PositivityTheory.ThKW.LatB.exists_move hG.cm hG.unram hP⟩⟩
    · rw [hc, hl, ← pow_mul, mul_comm, pow_mul, hu2, hev.neg_pow]
      push_cast
      rfl
    · obtain ⟨-, -, -, j, hj, hm⟩ := kept_deg hG hsq hs' hy P hq hqP hc hk
      rw [hc, hl, ← sqrt_pow_nat, hm, pow_mul, pow_mul, hu2, hsqr, hj.neg_pow]
  · have hu1 : u q = (Real.sqrt q : ℂ) := by simp only [u, if_neg hS, mul_one]
    rw [hc, hl, hu1, sqrt_pow_nat]
    exact ⟨hsqr _, fun hk => absurd ⟨P, hP, hfin, hqP, hk⟩ hS⟩

end UpperTheory.TP.W

end
