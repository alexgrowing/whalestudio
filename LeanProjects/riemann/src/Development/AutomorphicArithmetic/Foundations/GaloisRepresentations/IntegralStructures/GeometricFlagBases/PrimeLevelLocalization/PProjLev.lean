import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.StGood

open NumberField IsDedekindDomain GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc)
open UpperTheory.Gal.W2.Seed (Arith Setup)
open UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl

private theorem inId_zero {E : Type} [Field E] [NumberField E] (w : Plc E) (𝔟 : Ideal (𝓞 E)) : InId w 𝔟 0 :=
  ⟨0, zero_mem _, rfl⟩

private theorem nat_not_mem {E : Type} [Field E] [NumberField E] (w : Plc E) {q q' : ℕ} (hq : q.Prime) (hq' : q'.Prime)
    (hne : q' ≠ q) (h : (q' : 𝓞 E) ∈ w.asIdeal) : (q : 𝓞 E) ∉ w.asIdeal := by
  intro h2
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hq hq').2 hne.symm)
  have h1 : (a : 𝓞 E) * (q : 𝓞 E) + (b : 𝓞 E) * (q' : 𝓞 E) = 1 := by
    exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 E) hab
  exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (h1 ▸ add_mem (Ideal.mul_mem_left _ _ h2) (Ideal.mul_mem_left _ _ h)))

private theorem pow_not_mem {E : Type} [Field E] [NumberField E] (w : Plc E) {q : ℕ} (h : (q : 𝓞 E) ∉ w.asIdeal) (e : ℕ) :
    ((q ^ e : ℕ) : 𝓞 E) ∉ w.asIdeal := by
  push_cast
  exact fun h2 => h (w.isPrime.mem_of_pow_mem _ h2)

theorem UpperTheory.Gal.Int.Geo.Pl.projLev_of :
    Dict → PrimeProj → LevBasic → InIdUnit → ProjLev := by
  intro hD hP hL hU E _ _ _ A n p _ S F N v σ q' k hq' hne K₁ hK₁ u hu
  obtain ⟨π, hπ⟩ := hP E n q' hq'
  obtain ⟨g, rfl⟩ := F.surj u
  have hq := σ.atp.prime
  have hNpos : N.1 ≠ 0 := by have := N.2.1; omega
  have hN0 : (N.1 : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.2 hNpos
  obtain ⟨hu1, hu2⟩ := (σ.isLev (F.j g)).1 hu
  have hb : Ideal.span {((ordCompl[σ.q] N.1 : ℕ) : 𝓞 E)} * σ.𝔞 ≠ ⊥ := fun h => hN0 (by
    have := σ.mem
    rw [h] at this
    simpa using this)
  have hg3 := ((hD E A n p S F g).2.2.1 _ hb).1 hu2
  have hg2 := (hD E A n p S F g).2.1.1 hu1
  obtain ⟨-, -, -, -, e, he⟩ := σ.lv
  have hqe : ((σ.q ^ e : ℕ) : 𝓞 E) ∈ σ.𝔞 := by
    have h1 : (σ.q : 𝓞 E) ∈ uId S.D σ.q σ.r := Ideal.subset_span (Set.mem_insert _ _)
    have h2 := Ideal.pow_mem_pow h1 e
    push_cast
    exact he h2
  have hxK1 : F.j (π g) ∈ S.L.KN 1 := (hD E A n p S F (π g)).2.1.2 (fun w hw => by
    by_cases h : (q' : 𝓞 E) ∈ w.asIdeal
    · rw [(hπ g w).1 h]; exact hg2 w hw
    · rw [(hπ g w).2 h, mul_one, mul_inv_cancel]; exact one_mem _)
  have hNb : Ideal.span {(N.1 : 𝓞 E)} ≠ ⊥ := by simpa using hN0
  have hxN : F.j (π g) ∈ S.L.KN N.1 := by
    have lev := (hL p S.D S.G S.L).2.2.1 N.1
    refine (lev _).2 ⟨hxK1, ?_⟩
    refine ((hD E A n p S F (π g)).2.2.1 _ hNb).2 fun w hw i l => ?_
    by_cases h : (q' : 𝓞 E) ∈ w.asIdeal
    · have hc : F.cmp w (π g) = F.cmp w g := by simp only [Frame.cmp, (hπ g w).1 h]
      rw [hc]
      have hqw := nat_not_mem w hq hq' hne h
      have h1 := hg3 w hw i l
      rw [hU E w _ _ ⟨_, hqe, pow_not_mem w hqw e⟩] at h1
      have hspan : Ideal.span {(N.1 : 𝓞 E)} = Ideal.span {((ordCompl[σ.q] N.1 : ℕ) : 𝓞 E)} *
          Ideal.span {((σ.q ^ N.1.factorization σ.q : ℕ) : 𝓞 E)} := by
        rw [Ideal.span_singleton_mul_span_singleton, ← Nat.cast_mul, Nat.mul_comm,
          Nat.ordProj_mul_ordCompl_eq_self]
      rw [hspan, hU E w _ _ ⟨_, Ideal.mem_span_singleton_self _, pow_not_mem w hqw _⟩]
      exact h1
    · have hc : F.cmp w (π g) = 1 := by
        simp only [Frame.cmp, (hπ g w).2 h, mul_one, mul_inv_cancel, Units.val_one]
      rw [hc, sub_self]
      exact inId_zero w _
  refine ⟨F.j (π g), hxN, ?_⟩
  rw [← map_inv, ← map_mul]
  have hmul : ∀ w : Plc E, UpperTheory.Gal.CertificateRingHomMap.comp w ((π g)⁻¹ * g) = (UpperTheory.Gal.CertificateRingHomMap.comp w (π g))⁻¹ * UpperTheory.Gal.CertificateRingHomMap.comp w g := fun w => by
    rw [map_mul, map_inv]
  have hspan2 : Ideal.span {((ordCompl[σ.q] N.1 * q' ^ k : ℕ) : 𝓞 E)} * σ.𝔞 =
      (Ideal.span {((ordCompl[σ.q] N.1 : ℕ) : 𝓞 E)} * σ.𝔞) * Ideal.span {((q' ^ k : ℕ) : 𝓞 E)} := by
    rw [Nat.cast_mul, ← Ideal.span_singleton_mul_span_singleton]
    ring
  have hq'0 : ((q' ^ k : ℕ) : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.2 (pow_ne_zero _ hq'.ne_zero)
  have hBot : Ideal.span {((ordCompl[σ.q] N.1 * q' ^ k : ℕ) : 𝓞 E)} * σ.𝔞 ≠ ⊥ := by
    rw [hspan2]
    exact mul_ne_zero hb (by simpa using hq'0)
  refine (hK₁ _).2 ⟨?_, ?_⟩
  · rw [map_mul, map_inv]
    exact mul_mem (inv_mem hxK1) hu1
  · refine ((hD E A n p S F _).2.2.1 _ hBot).2 fun w hw i l => ?_
    by_cases h : (q' : 𝓞 E) ∈ w.asIdeal
    · have hc : F.cmp w ((π g)⁻¹ * g) = 1 := by
        simp only [Frame.cmp, hmul, (hπ g w).1 h, inv_mul_cancel, mul_one, mul_inv_cancel, Units.val_one]
      rw [hc, sub_self]
      exact inId_zero w _
    · have hc : F.cmp w ((π g)⁻¹ * g) = F.cmp w g := by
        simp only [Frame.cmp, hmul, (hπ g w).2 h, inv_one, one_mul]
      rw [hc, hspan2, hU E w _ _ ⟨_, Ideal.mem_span_singleton_self _, pow_not_mem w h k⟩]
      exact hg3 w hw i l
