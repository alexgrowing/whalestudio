import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.InIdBasic
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.PSiteTriv

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.L2.Host GlobalTheory.HeckeGal
open GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKDef
open GlobalTheory.LFun (KGL satEig)
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 Plc GLw AfQ sim mat comp rat loc lev SameK IsCen Shape IsForm IsKap mOf)
open UpperTheory.Gal.W2.Seed (Arith Setup)
open scoped TensorProduct Classical

namespace UpperTheory.Gal.Int.Geo.Pl

private theorem prime_under {E : Type} [Field E] [NumberField E] (u : Plc E) : ∃ l : ℕ, l.Prime ∧ (l : 𝓞 E) ∈ u.asIdeal := by
  haveI := u.isPrime
  haveI : Finite (𝓞 E ⧸ u.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ u.ne_bot
  refine ⟨ringChar (𝓞 E ⧸ u.asIdeal), CharP.char_is_prime (𝓞 E ⧸ u.asIdeal) _, Ideal.Quotient.eq_zero_iff_mem.1 ?_⟩
  rw [map_natCast]
  exact (ringChar.spec _ _).2 dvd_rfl

private theorem span_le_pow {R : Type} [CommRing R] {I : Ideal R} {l m e : ℕ} (hl : (l : R) ∈ I) (h : l ^ e ∣ m) :
    Ideal.span {(m : R)} ≤ I ^ e := by
  obtain ⟨c, rfl⟩ := h
  rw [Ideal.span_singleton_le_iff_mem, Nat.cast_mul, Nat.cast_pow]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hl e)

private theorem pow_le_prod {R ι : Type} [CommRing R] (T : Finset ι) (f : ι → Ideal R) (I : Ideal R) (e : ℕ) (h : ∀ u ∈ T, I ≤ f u) :
    I ^ (e * T.card) ≤ ∏ u ∈ T, f u ^ e := by
  rw [pow_mul, ← Finset.prod_const]
  exact Finset.prod_le_prod' fun u hu => Ideal.pow_right_mono (h u hu) e

private theorem prod_le_one {R ι : Type} [CommRing R] (T : Finset ι) (f : ι → Ideal R) (u : ι) (hu : u ∈ T) : ∏ u ∈ T, f u ≤ f u :=
  Ideal.le_of_dvd (Finset.dvd_prod_of_mem f hu)

theorem siteEx_of (hS : Sides) (hD : Dict) (hL : LevBasic) (hSt : StabOf) : SiteEx := by
  intro E _ _ _ A n p hp S F x U w₀ Up V hx hoff Q q hQ c hc hcp
  obtain ⟨T, e, hT, hst⟩ := hSt E A n p S F x U w₀ Up V hoff
  have key : ∀ (𝔟 : Ideal (𝓞 E)) (K : Subgroup S.G.GAf), 𝔟 ≠ ⊥ → (∀ u ∈ T, 𝔟 ≤ u.asIdeal ^ e) → IsLev S.L 𝔟 K →
      ∀ k ∈ K, Stab F V k := fun 𝔟 K h0 hle hK k hk => by
    obtain ⟨k', rfl⟩ := F.surj k
    obtain ⟨h1, h2⟩ := (hK _).1 hk
    refine hst k' h1 fun u hu i j => ?_
    obtain ⟨z, hz, hz'⟩ := ((hD E A n p S F k').2.2.1 𝔟 h0).1 h2 u (hT u hu).1 i j
    exact ⟨z, Ideal.map_mono (hle u hu) hz, hz'⟩
  choose l hl hlu using fun u : Plc E => prime_under u
  obtain ⟨t, ht, htp⟩ := Nat.exists_infinite_primes (Q.sup q + p + 3)
  have hr : ∀ q₀ : ℕ, ∃ r : ℤ, ∀ w ∈ Q, q w = q₀ → (q₀ : ℤ) ∣ r ^ 2 - A.tr * r + A.nm ∧ A.ω - (r : 𝓞 E) ∈ w.asIdeal := fun q₀ => by
    by_cases h : ∃ w ∈ Q, q w = q₀
    · obtain ⟨w', hw', rfl⟩ := h
      obtain ⟨a1, -, a3, a4, -, -⟩ := hQ w' hw'
      obtain ⟨-, -, -, -, -, ⟨r, hr, hω⟩, h7⟩ := hS E A x hx _ a1 a3.1 w' a4
      exact ⟨r, fun w hw h => ⟨hr, ((h7 r hω w).1 ((hQ w hw).2.2.2.2.2 w' hw' h)).2⟩⟩
    · exact ⟨0, fun w hw h' => (h ⟨w, hw, h'⟩).elim⟩
  choose r hr using hr
  obtain ⟨P, hP⟩ : ∃ P : ℕ, P = (∏ u ∈ T, l u) * ∏ w ∈ Q, q w := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M : ℕ, M = c * t * P ^ (e * T.card + e + 1) := ⟨_, rfl⟩
  have hP0 : 0 < P := hP ▸ Nat.mul_pos (Finset.prod_pos fun u _ => (hl u).pos) (Finset.prod_pos fun w hw => (hQ w hw).1.pos)
  have hPp : P.Coprime p := hP ▸ Nat.Coprime.mul_left
    (Nat.Coprime.prod_left fun u hu => (Nat.coprime_primes (hl u) hp.out).2 fun h => (hT u hu).1 (h ▸ hlu u))
    (Nat.Coprime.prod_left fun w hw => (Nat.coprime_primes (hQ w hw).1 hp.out).2 (hQ w hw).2.1)
  have hM0 : 0 < M := hM ▸ Nat.mul_pos (Nat.mul_pos hc htp.pos) (pow_pos hP0 _)
  have htM : t ∣ M := hM ▸ (dvd_mul_left t c).mul_right _
  have hMp : M.Coprime p := hM ▸ (hcp.mul_left ((Nat.coprime_primes htp hp.out).2 (by omega))).mul_left (hPp.pow_left _)
  have hpow : ∀ d k : ℕ, d ∣ P → k ≤ e * T.card + e + 1 → d ^ k ∣ M := fun d k hd hk =>
    hM ▸ ((pow_dvd_pow_of_dvd hd k).trans (pow_dvd_pow P hk)).mul_left _
  have hlP : ∀ u ∈ T, l u ∣ P := fun u hu => hP ▸ (Finset.dvd_prod_of_mem l hu).mul_right _
  have hqP : ∀ w ∈ Q, q w ∣ P := fun w hw => hP ▸ (Finset.dvd_prod_of_mem q hw).mul_left _
  have hM3 : 3 ≤ M := le_trans (by omega) (Nat.le_of_dvd hM0 htM)
  obtain ⟨L1, -, L3, -⟩ := hL p S.D S.G S.L
  let 𝔞 : ℕ → Ideal (𝓞 E) := fun q₀ => ∏ u ∈ T.filter (fun u => (q₀ : 𝓞 E) ∈ u.asIdeal), u.asIdeal ^ e
  have main : ∀ w ∈ Q, ∃ σ : Site S ⟨M, hM3, hMp⟩ w, σ.q = q w ∧ σ.r = r (q w) ∧ σ.𝔞 = 𝔞 (q w) ∧ ∀ k ∈ σ.K₀, Stab F V k := by
    intro w hw
    obtain ⟨a1, a2, a3, a4, a5, -⟩ := hQ w hw
    obtain ⟨r1, r2⟩ := hr _ w hw rfl
    obtain ⟨-, -, s3, -, -, -, s7⟩ := hS E A x hx _ a1 a3.1 w a4
    have hS' : ∀ u ∈ T.filter (fun u => (q w : 𝓞 E) ∈ u.asIdeal), u ∈ V.S := fun u hu =>
      (hT u (Finset.mem_filter.1 hu).1).2.elim id fun h => (h (F.a_int u _ a1 a3 (Finset.mem_filter.1 hu).2)).elim
    obtain ⟨K, hK⟩ := L1 (Ideal.span {((ordCompl[q w] M : ℕ) : 𝓞 E)} * 𝔞 (q w))
    have hmem : ((M : ℕ) : 𝓞 E) ∈ Ideal.span {((ordCompl[q w] M : ℕ) : 𝓞 E)} * 𝔞 (q w) := by
      have h1 : e * (T.filter (fun u => (q w : 𝓞 E) ∈ u.asIdeal)).card ≤ M.factorization (q w) :=
        (a1.pow_dvd_iff_le_factorization hM0.ne').1 (hpow _ _ (hqP w hw)
          ((Nat.mul_le_mul_left e (Finset.card_filter_le _ _)).trans (by omega)))
      have h2 : ((ordProj[q w] M : ℕ) : 𝓞 E) ∈ 𝔞 (q w) := by
        refine pow_le_prod _ (fun u : Plc E => u.asIdeal) (Ideal.span {(q w : 𝓞 E)}) e
          (fun u hu => (Ideal.span_singleton_le_iff_mem _).2 (Finset.mem_filter.1 hu).2) ?_
        refine Ideal.pow_le_pow_right h1 ?_
        rw [Nat.cast_pow]
        exact Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) _
      have h3 := Ideal.mul_mem_mul (Ideal.mem_span_singleton_self ((ordCompl[q w] M : ℕ) : 𝓞 E)) h2
      rwa [← Nat.cast_mul, Nat.mul_comm, Nat.ordProj_mul_ordCompl_eq_self] at h3
    have htq : ¬ q w ∣ t := fun h => by
      have := (Nat.prime_dvd_prime_iff_eq a1 htp).1 h
      have := Finset.le_sup (f := q) hw
      omega
    refine ⟨⟨q w, r (q w), 𝔞 (q w), K, a3, atPrime_of S a1 a2 a3 r1 a4 r2, ⟨?_, (Nat.coprime_ordCompl a1 hM0.ne').symm,
      hMp.coprime_dvd_left (Nat.ordCompl_dvd _ _), ?_, ?_⟩, hK, hmem⟩, rfl, rfl, rfl, key _ K (fun h => ?_) (fun u hu => ?_) hK⟩
    · exact le_trans (by omega) (Nat.le_of_dvd (Nat.ordCompl_pos _ hM0.ne') (Nat.dvd_ordCompl_of_dvd_not_dvd htM htq))
    · refine Ideal.isCoprime_iff_sup_eq.1 (IsCoprime.prod_left fun u hu => IsCoprime.pow_left ?_)
      exact HeightOneSpectrum.isCoprime_of_ne u w fun h => a5.2.1 (h ▸ hS' u hu)
    · refine ⟨_, pow_le_prod _ (fun u : Plc E => u.asIdeal) _ e fun u hu => Ideal.span_le.2 ?_⟩
      have hq := (Finset.mem_filter.1 hu).2
      have := ((s7 _ r2 u).1 ((s3 u hq).resolve_right (a5.2.2.2.1 u (hS' u hu)))).2
      rintro y (rfl | rfl)
      exacts [hq, this]
    · rw [h, Ideal.mem_bot] at hmem
      exact hM0.ne' (Nat.cast_eq_zero.1 hmem)
    · by_cases hq : (q w : 𝓞 E) ∈ u.asIdeal
      · exact Ideal.mul_le_right.trans (prod_le_one _ (fun u : Plc E => u.asIdeal ^ e) u (Finset.mem_filter.2 ⟨hu, hq⟩))
      · refine Ideal.mul_le_left.trans (span_le_pow (hlu u) (Nat.dvd_ordCompl_of_dvd_not_dvd (hpow _ e (hlP u hu) (by omega)) fun h => hq ?_))
        rw [(Nat.prime_dvd_prime_iff_eq a1 (hl u)).1 (a1.dvd_of_dvd_pow h)]
        exact hlu u
  choose σ h1 h2 h3 h4 using main
  refine ⟨⟨M, hM3, hMp⟩, σ, hM ▸ (dvd_mul_right c t).mul_right _, key (Ideal.span {(M : 𝓞 E)}) _ ?_ (fun u hu => ?_) (L3 M),
    fun w hw => ⟨?_, h1 w hw, h4 w hw⟩, fun w hw w' hw' h => ?_⟩
  · rw [Ne, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero]
    exact hM0.ne'
  · exact span_le_pow (hlu u) (hpow _ _ (hlP u hu) (by omega))
  · simpa using hpow _ 1 (hqP w hw) (by omega)
  · rw [h1, h1] at h
    rw [h2, h2, h3, h3, h]
    exact ⟨rfl, rfl⟩

end UpperTheory.Gal.Int.Geo.Pl
