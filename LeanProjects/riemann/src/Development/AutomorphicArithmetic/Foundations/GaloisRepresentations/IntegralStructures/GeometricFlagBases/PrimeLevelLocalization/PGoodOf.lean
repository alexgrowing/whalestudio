import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.StGood

set_option autoImplicit false

open NumberField IsDedekindDomain GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc)
open UpperTheory.Gal.W2.Seed (Arith Setup)
open UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl

namespace UpperTheory.Gal.Int.Geo.Pl.GoodPlacesAlt

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} {L : Link D G} {N : Lv p}

private def Row (q : ℕ) (r : ℤ) (N₀ : ℕ) (𝔞 : Ideal (𝓞 D.F)) (K₀ : Subgroup G.GAf) (𝔴 : Ideal (𝓞 D.F)) (g : Mem L N) : Prop :=
  ∃ (c : ℕ) (𝔞' : Ideal (𝓞 D.F)) (K₁ : Subgroup G.GAf) (h₁ h₂ : G.GAf) (N₁ : Lv p), LevAt D q r 𝔴 (N₀ * c) 𝔞' ∧
      IsLev L (Ideal.span {((N₀ * c : ℕ) : 𝓞 D.F)} * 𝔞') K₁ ∧ 𝔞' ≤ 𝔞 ∧ L.KN g.M.1 ≤ K₁ ∧
      ((g.M.1 : ℕ) : 𝓞 D.F) ∈ Ideal.span {((N₀ * c : ℕ) : 𝓞 D.F)} * 𝔞' ∧
      (∀ u ∈ K₀, ∃ x ∈ g.K, x ∈ K₀ ∧ x⁻¹ * u ∈ K₁) ∧ g.h = h₁ * h₂ ∧ Integ L h₁ ∧ Integ L h₂ ∧
      (∀ v ∈ LaHat D, ∃ v' ∈ LaHat D, L.actG h₂ v' = c • v) ∧ ((N₁.1 : ℕ) : 𝓞 D.F) ∈ Ideal.span {(N₀ : 𝓞 D.F)} * 𝔞' ∧
      (∀ k ∈ g.K, ∀ u ∈ L.KN g.M.1, h₂ * k * u * (h₂ * k)⁻¹ ∈ L.KN N₁.1) ∧
      (∀ u ∈ L.KN N₁.1, h₁ * u * h₁⁻¹ ∈ L.KN N.1) ∧
      (h₁ = 1 ∨ ∃ (𝔴' : Ideal (𝓞 D.F)) (i : ℕ), 𝔴'.IsMaximal ∧ uId D q r ≤ 𝔴' ∧ 𝔞' ≤ 𝔞 * 𝔴' ∧ i ≤ D.n ∧
        Ideal.absNorm 𝔴' ^ i ∣ N₁.1 ∧ IsTjElt L q r 𝔴' i h₁)

private theorem kn_le
    (hle : ∀ 𝔟 𝔟' K K', IsLev L 𝔟 K → IsLev L 𝔟' K' → 𝔟 ≤ 𝔟' → K ≤ K')
    (hKN : ∀ N : ℕ, IsLev L (Ideal.span {(N : 𝓞 D.F)}) (L.KN N))
    {𝔟 : Ideal (𝓞 D.F)} {K : Subgroup G.GAf} {M : ℕ} (hK : IsLev L 𝔟 K) (hM : (M : 𝓞 D.F) ∈ 𝔟) : L.KN M ≤ K :=
  hle _ _ _ _ (hKN M) hK ((Ideal.span_singleton_le_iff_mem _).2 hM)

private theorem row_trans
    (hle : ∀ 𝔟 𝔟' K K', IsLev L 𝔟 K → IsLev L 𝔟' K' → 𝔟 ≤ 𝔟' → K ≤ K')
    (hKN : ∀ N : ℕ, IsLev L (Ideal.span {(N : 𝓞 D.F)}) (L.KN N))
    {q : ℕ} {r : ℤ} {N₀ : ℕ} {𝔞 𝔴 : Ideal (𝓞 D.F)} {K₀ K₁ : Subgroup G.GAf} {c : ℕ}
    (hlv : LevAt D q r 𝔴 N₀ 𝔞) (hN : ((N.1 : ℕ) : 𝓞 D.F) ∈ Ideal.span {(N₀ : 𝓞 D.F)} * 𝔞)
    (hc : 0 < c) (hcq : c.Coprime q) (hcp : c.Coprime p)
    (hK₁ : IsLev L (Ideal.span {((N₀ * c : ℕ) : 𝓞 D.F)} * 𝔞) K₁)
    (g : Mem L N) (hM : g.M.1 = N.1 * c)
    (hback : ∀ v ∈ LaHat D, ∃ v' ∈ LaHat D, L.actG g.h v' = c • v)
    (hx : ∀ u ∈ K₀, ∃ x ∈ g.K, x ∈ K₀ ∧ x⁻¹ * u ∈ K₁) : Row q r N₀ 𝔞 K₀ 𝔴 g := by
  obtain ⟨h3, hq, hp, hv, e, he⟩ := hlv
  have hmem : ((g.M.1 : ℕ) : 𝓞 D.F) ∈ Ideal.span {((N₀ * c : ℕ) : 𝓞 D.F)} * 𝔞 := by
    obtain ⟨a, ha, ea⟩ := Ideal.mem_span_singleton_mul.1 hN
    refine Ideal.mem_span_singleton_mul.2 ⟨a, ha, ?_⟩
    rw [hM]; push_cast; rw [← ea]; ring
  refine ⟨c, 𝔞, K₁, 1, g.h, N, ⟨le_trans h3 (Nat.le_mul_of_pos_right _ hc), Nat.coprime_mul_iff_left.2 ⟨hq, hcq⟩,
    Nat.coprime_mul_iff_left.2 ⟨hp, hcp⟩, hv, e, he⟩, hK₁, le_rfl, kn_le hle hKN hK₁ hmem, hmem, hx,
    (one_mul _).symm, integ_of_mem (one_mem _), g.int, hback, hN, fun k hk u hu => g.adm k hk u hu, ?_, Or.inl rfl⟩
  intro u hu
  simpa using hu

private theorem row_near
    (hex : ∀ 𝔟, ∃ K, IsLev L 𝔟 K)
    (hle : ∀ 𝔟 𝔟' K K', IsLev L 𝔟 K → IsLev L 𝔟' K' → 𝔟 ≤ 𝔟' → K ≤ K')
    (hKN : ∀ N : ℕ, IsLev L (Ideal.span {(N : 𝓞 D.F)}) (L.KN N))
    (hnorm : ∀ 𝔟 K, IsLev L 𝔟 K → ∀ k ∈ L.KN 1, ∀ u ∈ K, k * u * k⁻¹ ∈ K)
    {q : ℕ} {r : ℤ} {N₀ : ℕ} {𝔞 𝔴 𝔴' : Ideal (𝓞 D.F)} {K₀ : Subgroup G.GAf} {i : ℕ}
    (hlv : LevAt D q r 𝔴 N₀ 𝔞) (hN : ((N.1 : ℕ) : 𝓞 D.F) ∈ Ideal.span {(N₀ : 𝓞 D.F)} * 𝔞)
    (hmax : 𝔴.IsMaximal) (hmax' : 𝔴'.IsMaximal) (hne : 𝔴' ≠ 𝔴) (hu : uId D q r ≤ 𝔴')
    (hi : 0 < i) (hin : i ≤ D.n) (g : Mem L N) (hK : g.K = K₀) (hM : g.M.1 = N.1 * Ideal.absNorm 𝔴' ^ i)
    (hT : IsTjElt L q r 𝔴' i g.h) : Row q r N₀ 𝔞 K₀ 𝔴 g := by
  obtain ⟨h3, hq, hp, hv, e, he⟩ := hlv
  obtain ⟨K₁, hK₁⟩ := hex (Ideal.span {((N₀ * 1 : ℕ) : 𝓞 D.F)} * (𝔞 * 𝔴'))
  have hmem : ((g.M.1 : ℕ) : 𝓞 D.F) ∈ Ideal.span {(N₀ : 𝓞 D.F)} * (𝔞 * 𝔴') := by
    rw [← mul_assoc, hM]
    obtain ⟨i, rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    have hn : ((Ideal.absNorm 𝔴' : ℕ) : 𝓞 D.F) ∈ 𝔴' := Ideal.absNorm_mem 𝔴'
    have : ((N.1 * Ideal.absNorm 𝔴' ^ (i + 1) : ℕ) : 𝓞 D.F)
        = (((N.1 : ℕ) : 𝓞 D.F) * ((Ideal.absNorm 𝔴' : ℕ) : 𝓞 D.F) ^ i) * ((Ideal.absNorm 𝔴' : ℕ) : 𝓞 D.F) := by
      push_cast; ring
    rw [this]
    exact Ideal.mul_mem_mul (Ideal.mul_mem_right _ _ hN) hn
  have hmem1 : ((g.M.1 : ℕ) : 𝓞 D.F) ∈ Ideal.span {((N₀ * 1 : ℕ) : 𝓞 D.F)} * (𝔞 * 𝔴') := by
    simpa using hmem
  refine ⟨1, 𝔞 * 𝔴', K₁, g.h, 1, g.M, ⟨by simpa using h3, by simpa using hq, by simpa using hp, ?_, e + 1, ?_⟩, hK₁,
    Ideal.mul_le_left, kn_le hle hKN hK₁ hmem1, hmem1, ?_, (mul_one _).symm, g.int, integ_of_mem (one_mem _), ?_,
    hmem, ?_, ?_, Or.inr ⟨𝔴', i, hmax', hu, le_rfl, hin, by rw [hM]; exact Dvd.intro_left _ rfl, hT⟩⟩
  · exact Ideal.isCoprime_iff_sup_eq.1 (IsCoprime.mul_left (Ideal.isCoprime_iff_sup_eq.2 hv)
      (Ideal.isCoprime_iff_sup_eq.2 (Ideal.IsMaximal.coprime_of_ne hmax' hmax hne)))
  · rw [pow_succ]; exact Ideal.mul_mono he hu
  · intro u hu'
    exact ⟨u, hK ▸ hu', hu', by simpa using one_mem K₁⟩
  · intro v hv'
    exact ⟨v, hv', by simp⟩
  · intro k hk u hu'
    have := hnorm _ _ (hKN g.M.1) k (g.le_one hk) u hu'
    simpa using this
  · intro u hu'
    have := g.adm 1 (one_mem _) u hu'
    simpa using this

private theorem absNorm_nat {E : Type} [Field E] [NumberField E] (q : ℕ) :
    Ideal.absNorm (Ideal.span {((q : ℕ) : 𝓞 E)}) = q ^ Module.finrank ℤ (𝓞 E) := by
  rw [Ideal.absNorm_span_singleton, show ((q : ℕ) : 𝓞 E) = algebraMap ℤ (𝓞 E) (q : ℤ) by simp,
    Algebra.norm_algebraMap]
  simp [Int.natAbs_pow]

end UpperTheory.Gal.Int.Geo.Pl.GoodPlacesAlt

open UpperTheory.Gal.Int.Geo.Pl.GoodPlacesAlt in
theorem UpperTheory.Gal.Int.Geo.Pl.goodOf_of :
    LevBasic → TjOK → ProjLev → GoodOf := by
  intro hL hT hP E _ _ _ A n p _ S F x hx N v σ J L' _ g θ hD hj
  obtain ⟨hex, hle, hKN, -, hnorm, -⟩ := hL p S.D S.G S.L
  refine ⟨σ.q, σ.r, ordCompl[σ.q] N.1, σ.𝔞, σ.K₀, σ.atp, σ.lv, σ.isLev, kn_le hle hKN σ.isLev σ.mem, σ.mem, hD,
    fun j => ?_⟩
  have hK₀ : IsLev S.L (Ideal.span {((ordCompl[σ.q] N.1 * 1 : ℕ) : 𝓞 E)} * σ.𝔞) σ.K₀ := by
    simpa using σ.isLev
  change Row σ.q σ.r (ordCompl[σ.q] N.1) σ.𝔞 σ.K₀ v.asIdeal (g j)
  rcases hj j with ⟨hK, hM, hh⟩ | ⟨w, σ', i, hne, hc, hi, hK, hH, hM⟩
  · refine row_trans hle hKN σ.lv σ.mem one_pos (Nat.coprime_one_left _) (Nat.coprime_one_left _) hK₀ (g j) (by simp [hM]) ?_ ?_
    · intro v' hv'
      refine ⟨S.L.actG (g j).h⁻¹ v', integ_of_mem (inv_mem hh) v' hv', ?_⟩
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
      simp
    · intro u hu
      exact ⟨1, one_mem _, one_mem _, by simpa using hu⟩
  · obtain ⟨hI, hTj⟩ := hT E A n p S F x hx N w σ' i hi _ hH
    by_cases hq : σ.q = σ'.q
    · obtain ⟨hr, ha⟩ := hc hq
      have hKe : σ'.K₀ = σ.K₀ := by
        have h' := σ'.isLev
        rw [← hq, ← ha] at h'
        exact Subgroup.ext fun y => (h' y).trans (σ.isLev y).symm
      rw [hKe] at hK
      have hat := σ'.atp
      rw [← hq, ← hr] at hTj hat
      rcases Nat.eq_zero_or_pos i with rfl | hpos
      · refine row_trans hle hKN σ.lv σ.mem one_pos (Nat.coprime_one_left _) (Nat.coprime_one_left _) hK₀ (g j) (by simpa using hM) ?_ ?_
        · intro v' hv'
          obtain ⟨y, hy, e⟩ := hTj.back v' hv'
          exact ⟨y, hy, by simpa using e⟩
        · intro u hu
          exact ⟨1, one_mem _, one_mem _, by simpa using hu⟩
      · exact row_near hex hle hKN hnorm σ.lv σ.mem σ.atp.max hat.max
          (fun e => hne (HeightOneSpectrum.ext e)) hat.le hpos hi (g j) hK hM hTj
    · have hat := σ'.atp
      have hqw : ((σ'.q : ℕ) : 𝓞 E) ∈ w.asIdeal := hat.le (Ideal.subset_span (Set.mem_insert _ _))
      have hdvd : Ideal.absNorm w.asIdeal ∣ σ'.q ^ Module.finrank ℤ (𝓞 E) := by
        have := Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 hqw)
        rwa [absNorm_nat] at this
      obtain ⟨f, -, hf⟩ := (Nat.dvd_prime_pow hat.prime).1 hdvd
      have hcpow : Ideal.absNorm w.asIdeal ^ i = σ'.q ^ (f * i) := by rw [hf, pow_mul]
      obtain ⟨K₁, hK₁⟩ := hex (Ideal.span {((ordCompl[σ.q] N.1 * σ'.q ^ (f * i) : ℕ) : 𝓞 E)} * σ.𝔞)
      have hcq : (σ'.q ^ (f * i)).Coprime σ.q :=
        Nat.Coprime.pow_left _ ((Nat.coprime_primes hat.prime σ.atp.prime).2 (Ne.symm hq))
      have hcp : (σ'.q ^ (f * i)).Coprime p :=
        Nat.Coprime.pow_left _ ((Nat.coprime_primes hat.prime (Fact.out)).2 hat.ne)
      refine row_trans hle hKN σ.lv σ.mem (pow_pos hat.prime.pos _) hcq hcp hK₁ (g j) (by rw [hM, hcpow]) ?_ ?_
      · rw [← hcpow]; exact hTj.back
      · intro u hu
        obtain ⟨y, hy, e⟩ := hP E A n p S F N v σ σ'.q (f * i) hat.prime (Ne.symm hq) K₁ hK₁ u hu
        exact ⟨y, hK ▸ kn_le hle hKN σ'.isLev σ'.mem hy, kn_le hle hKN σ.isLev σ.mem hy, e⟩
