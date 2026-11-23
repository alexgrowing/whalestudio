import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BaseDataEmbeddingConj
import Formalism.LocalToGlobal.Columns.BaseLemmas
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NcardPrimesOverOfStabilizer
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.EqOfLeOfAbsNormEq

open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open Formalism.L2.Col

namespace GlobalTheory.BasePrimes

section General

variable {E : Type} [Field E] [NumberField E]

theorem prod_absNorm_divs_dvd {a : 𝓞 E} (ha : a ≠ 0) :
    ∏ P ∈ divs a, Ideal.absNorm P.asIdeal ∣ Ideal.absNorm (Ideal.span {a}) := by
  rw [← map_prod]
  apply map_dvd
  refine Finset.prod_dvd_of_coprime ?_ ?_
  · intro P _ Q _ hPQ
    exact (HeightOneSpectrum.isCoprime_of_ne P Q hPQ)
  · intro P hP
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
    exact (mem_divs ha P).1 hP

theorem le_absNorm_of_mem {p : ℕ} (hp : p.Prime) (P : HeightOneSpectrum (𝓞 E)) (h : (p : 𝓞 E) ∈ P.asIdeal) :
    p ≤ Ideal.absNorm P.asIdeal := by
  have h1 : Ideal.absNorm P.asIdeal ∣ p ^ Module.finrank ℚ E := by
    rw [← RingOfIntegers.rank, ← Ideal.absNorm_span_natCast]
    exact Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 h)
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp).1 h1
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rw [pow_zero, Ideal.absNorm_eq_one_iff] at hk
    exact absurd hk P.isPrime.ne_top
  · rw [hk]
    exact Nat.le_self_pow hk0.ne' p

theorem absNorm_eq_of_split {p : ℕ} (hp : p.Prime) (h : (divs (p : 𝓞 E)).card = Module.finrank ℚ E)
    (P : HeightOneSpectrum (𝓞 E)) (hP : (p : 𝓞 E) ∈ P.asIdeal) : Ideal.absNorm P.asIdeal = p := by
  have hp0 : (p : 𝓞 E) ≠ 0 := by exact_mod_cast hp.ne_zero
  have h1 := prod_absNorm_divs_dvd hp0
  rw [Ideal.absNorm_span_natCast, RingOfIntegers.rank, ← h] at h1
  have h2 := Nat.le_of_dvd (pow_pos hp.pos _) h1
  by_contra hne
  have hlt : p < Ideal.absNorm P.asIdeal := lt_of_le_of_ne (le_absNorm_of_mem hp P hP) (Ne.symm hne)
  have h3 : ∏ _Q ∈ divs (p : 𝓞 E), p < ∏ Q ∈ divs (p : 𝓞 E), Ideal.absNorm Q.asIdeal :=
    Finset.prod_lt_prod (fun _ _ => hp.pos) (fun Q hQ => le_absNorm_of_mem hp Q ((mem_divs hp0 Q).1 hQ))
      ⟨P, (mem_divs hp0 P).2 hP, hlt⟩
  rw [Finset.prod_const] at h3
  omega

theorem card_divs_map_le (s : 𝓞 E →+* 𝓞 E) (hs : Function.Surjective s) {a : 𝓞 E} (ha : a ≠ 0) (hsa : s a ≠ 0) :
    (divs (s a)).card ≤ (divs a).card := by
  refine Finset.card_le_card_of_injOn (fun P => HeightOneSpectrum.comap s hs P) ?_ ?_
  · intro P hP
    have h1 := (mem_divs hsa P).1 hP
    exact (mem_divs ha _).2 h1
  · intro P _ Q _ hPQ
    apply HeightOneSpectrum.ext
    exact Ideal.comap_injective_of_surjective s hs (congrArg HeightOneSpectrum.asIdeal hPQ)

theorem split_facts (s : 𝓞 E →+* 𝓞 E) (hs : ∀ x, s (s x) = x) {p f : ℕ} (hp : p.Prime)
    (hf : Module.finrank ℚ E = 2 * f) (h : (placesOver E p).ncard = Module.finrank ℚ E) {a : 𝓞 E}
    (ha : a * s a = (p : 𝓞 E)) :
    IsCoprime a (s a) ∧ ((divs a).card = f ∧ ∀ P ∈ divs a, Ideal.absNorm P.asIdeal = p) ∧
      ((divs (s a)).card = f ∧ ∀ P ∈ divs (s a), Ideal.absNorm P.asIdeal = p) := by
  classical
  have hp0 : (p : 𝓞 E) ≠ 0 := by exact_mod_cast hp.ne_zero
  have ha0 : a ≠ 0 := left_ne_zero_of_mul (ha ▸ hp0)
  have hb0 : s a ≠ 0 := right_ne_zero_of_mul (ha ▸ hp0)
  have hsurj : Function.Surjective s := fun x => ⟨s x, hs x⟩
  have hc : (divs (p : 𝓞 E)).card = Module.finrank ℚ E := by
    rw [← h, ← Set.ncard_coe_finset]
    congr 1
    ext P
    exact mem_divs hp0 P
  have hna : ∀ P ∈ divs a, Ideal.absNorm P.asIdeal = p := fun P hP =>
    absNorm_eq_of_split hp hc P (ha ▸ Ideal.mul_mem_right _ _ ((mem_divs ha0 P).1 hP))
  have hnb : ∀ P ∈ divs (s a), Ideal.absNorm P.asIdeal = p := fun P hP =>
    absNorm_eq_of_split hp hc P (ha ▸ Ideal.mul_mem_left _ _ ((mem_divs hb0 P).1 hP))
  have hU : divs (p : 𝓞 E) = divs a ∪ divs (s a) := by
    ext P
    rw [Finset.mem_union, mem_divs hp0, mem_divs ha0, mem_divs hb0, ← ha]
    exact P.isPrime.mul_mem_iff_mem_or_mem
  have hle : (divs a).card + (divs (s a)).card ≤ Module.finrank ℚ E := by
    have h1 := prod_absNorm_divs_dvd ha0
    have h2 := prod_absNorm_divs_dvd hb0
    rw [Finset.prod_congr rfl hna, Finset.prod_const] at h1
    rw [Finset.prod_congr rfl hnb, Finset.prod_const] at h2
    have h3 := mul_dvd_mul h1 h2
    rw [← pow_add, ← map_mul, Ideal.span_singleton_mul_span_singleton, ha, Ideal.absNorm_span_natCast,
      RingOfIntegers.rank] at h3
    exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 h3
  have hui := Finset.card_union_add_card_inter (divs a) (divs (s a))
  rw [← hU, hc] at hui
  have e1 := card_divs_map_le s hsurj ha0 hb0
  have e2 := card_divs_map_le s hsurj hb0 (by rw [hs]; exact ha0)
  rw [hs] at e2
  have hint : divs a ∩ divs (s a) = ∅ := Finset.card_eq_zero.1 (by omega)
  refine ⟨?_, ⟨by omega, hna⟩, ⟨by omega, hnb⟩⟩
  rw [← Ideal.isCoprime_span_singleton_iff, Ideal.isCoprime_iff_sup_eq]
  by_contra hne
  obtain ⟨M, hM, hle'⟩ := Ideal.exists_le_maximal _ hne
  have haM : a ∈ M := hle' (Ideal.mem_sup_left (Ideal.mem_span_singleton_self a))
  have hbM : s a ∈ M := hle' (Ideal.mem_sup_right (Ideal.mem_span_singleton_self (s a)))
  have hM0 : M ≠ ⊥ := fun h0 => ha0 (by rwa [h0, Ideal.mem_bot] at haM)
  have hmem : (⟨M, hM.isPrime, hM0⟩ : HeightOneSpectrum (𝓞 E)) ∈ divs a ∩ divs (s a) :=
    Finset.mem_inter.2 ⟨(mem_divs ha0 _).2 haM, (mem_divs hb0 _).2 hbM⟩
  rw [hint] at hmem
  exact Finset.notMem_empty _ hmem

theorem modEq_one_of_dvd (s : 𝓞 E →+* 𝓞 E) {a : 𝓞 E} {T c : ℕ} (ha : a * s a = (T : 𝓞 E))
    (h : (c : 𝓞 E) ∣ a - 1) : T ≡ 1 [MOD c] := by
  obtain ⟨y, hy⟩ := h
  have h1 : a = 1 + (c : 𝓞 E) * y := by
    rw [← hy]
    ring
  have h2 : s a = 1 + (c : 𝓞 E) * s y := by
    rw [h1, map_add, map_one, map_mul, map_natCast]
  have h3 : (c : 𝓞 E) ∣ (((T : ℤ) - 1 : ℤ) : 𝓞 E) := by
    refine ⟨y + s y + (c : 𝓞 E) * (y * s y), ?_⟩
    push_cast
    rw [← ha, h2]
    nth_rewrite 1 [h1]
    ring
  exact (Nat.modEq_iff_dvd.2 (Primes.natCast_dvd_intCast h3)).symm

end General

theorem conjO_conjO (B : Base) (x : 𝓞 B.fields.E) : B.fields.conjO (B.fields.conjO x) = x := by
  letI := B.fields.starE
  apply RingOfIntegers.ext
  exact star_star (x : B.fields.E)

theorem finrank_E (B : Base) : Module.finrank ℚ B.fields.E = 2 * B.fields.f := by
  rw [B.fields_f]
  show Module.finrank ℚ B.host.E = _
  rw [B.host.finrank_cmField]
  unfold Ranks.f Ranks.n
  ring

theorem mem_Kq (B : Base) {x : B.host.E} (hx : x ∈ B.host.K) : x ∈ B.fields.Kq := by
  intro τ τ'
  rw [B.fields_emb_apply, B.fields_emb_apply, Formalism.MainNotions.UnusedSlot33.HK.sigmaOf_fix_K B.host _ τ.2 x hx,
    Formalism.MainNotions.UnusedSlot33.HK.sigmaOf_fix_K B.host _ τ'.2 x hx]

theorem primes_ok : ∀ (B : Base) (X : PreX B.toPre), (B.primes X).Ok ∧ (B.primes X).PiGCong := by
  intro B X
  have hG := fun i => split_facts B.fields.conjO (conjO_conjO B) (B.host.g_prime i) (finrank_E B)
    (GlobalTheory.HostSplit.split_of_one_mod B.R B.host _ (B.host.g_prime i) (B.g_cond i)).1 (B.primes_piG_norm X i)
  have hT := fun u => split_facts B.fields.conjO (conjO_conjO B) (B.T_prime u) (finrank_E B)
    (GlobalTheory.HostSplit.split_of_one_mod B.R B.host _ (B.T_prime u) (B.T_cond u)).1 (B.primes_piT_norm X u)
  refine ⟨?_, B.primes_piGCong X⟩
  refine
    { g_prime := B.host.g_prime
      piG_Kq := fun i => mem_Kq B (X.piG_K i)
      piG_norm := B.primes_piG_norm X
      piG_cop := fun i => (hG i).1
      vG_card := fun i => (hG i).2.2.1
      vG_norm := fun i => (hG i).2.2.2
      g_cong := (B.primes_piGCong X).g_cong (B.primes_piG_norm X)
      g_ne := B.host.g_ne
      T_prime := B.T_prime
      piT_Kq := fun u => mem_Kq B (X.piT_K u)
      piT_norm := B.primes_piT_norm X
      piT_cop := fun u => (hT u).1
      vT_card := fun u => (hT u).2.1.1
      vT_norm := fun u => (hT u).2.1.2
      piT_cong := X.piT_cong
      T_ne_g := fun u i hi => ?_ }
  have h1 := modEq_one_of_dvd B.fields.conjO (B.primes_piT_norm X u) (X.piT_cong u)
  have hd : B.host.g i ∣ B.host.QS * B.host.q * B.host.d * (B.host.g 0 * B.host.g 1) ^ 2 := by
    refine Dvd.dvd.mul_left (Dvd.dvd.pow ?_ two_ne_zero) _
    fin_cases i
    · exact dvd_mul_right _ _
    · exact dvd_mul_left _ _
  have h2 : B.host.g i ≡ 1 [MOD B.host.g i] := by
    have h3 := h1.of_dvd hd
    rwa [hi] at h3
  have h4 : B.host.g i ∣ 1 := (Nat.modEq_zero_iff_dvd.1 (h2.symm.trans (Nat.modEq_zero_iff_dvd.2 dvd_rfl)))
  exact (B.host.g_prime i).one_lt.ne' (Nat.dvd_one.1 h4)

end GlobalTheory.BasePrimes
