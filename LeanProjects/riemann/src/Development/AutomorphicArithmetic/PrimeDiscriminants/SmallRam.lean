import Mathlib
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts

open NumberField IsDedekindDomain Ideal

noncomputable section

namespace Formalism.HC.HostAx

variable {φ : Frame} (H : HostAx φ)

theorem mem_sq_of_dvd_QS (hE : H.toHostRaw.Exact) {l : ℕ} (hl : l.Prime) (hd : l ∣ H.QS) (P : Ideal (𝓞 H.E)) [hP : P.IsPrime]
    (hm : (l : 𝓞 H.E) ∈ P) : (l : 𝓞 H.E) ∈ P ^ 2 := by
  have hEgal := H.galois
  have : IsGaloisGroup Gal(H.E/ℚ) ℤ (𝓞 H.E) := IsGaloisGroup.of_isFractionRing _ _ _ ℚ H.E
  have : Fact l.Prime := ⟨hl⟩
  have hlz : Prime (l : ℤ) := Nat.prime_iff_prime_int.1 hl
  have hsp : (span {(l : ℤ)}).IsPrime := (Ideal.span_singleton_prime hlz.ne_zero).2 hlz
  have hne : span {(l : ℤ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact hlz.ne_zero
  have hlo : P.LiesOver (span {(l : ℤ)}) := (Ideal.liesOver_span_iff hP.ne_top hlz).2 (by simpa using hm)
  obtain ⟨u, hu, hu1⟩ := hE l hl hd
  have hN : l ∣ H.condN := hd.trans H.QS_dvd_condN
  have hdiv : ordCompl[l] H.condN ∣ H.condN / l := by
    have h1 : 1 ≤ H.condN.factorization l := (hl.dvd_iff_one_le_factorization H.condN_ne_zero).1 hN
    exact Nat.div_dvd_div_left (Nat.ordProj_dvd _ _) (by simpa using pow_dvd_pow l h1)
  have hin : ∀ x : 𝓞 H.E, H.gal.symm (H.art u) • x - x ∈ P :=
    (H.der.inertia l P _).2 ⟨u, hu.of_dvd hdiv, H.gal.apply_symm_apply _⟩
  have hnt : 1 < Nat.card (P.inertia Gal(H.E/ℚ)) := by
    rw [Finite.one_lt_card_iff_nontrivial]
    refine ⟨⟨⟨_, AddSubgroup.mem_inertia.2 hin⟩, 1, fun h1 => hu1 ?_⟩⟩
    have h2 : H.gal.symm (H.art u) = 1 := congrArg Subtype.val h1
    simpa using congrArg H.gal h2
  rw [card_inertia_eq_ramificationIdxIn (G := Gal(H.E/ℚ)) (span {(l : ℤ)}) P,
    ramificationIdxIn_eq_ramificationIdx (span {(l : ℤ)}) P Gal(H.E/ℚ),
    ← ramificationIdx'_eq_ramificationIdx (span {(l : ℤ)}) P hne] at hnt
  have hle : Ideal.map (algebraMap ℤ (𝓞 H.E)) (span {(l : ℤ)}) ≤ P ^ 2 := le_pow_of_le_ramificationIdx' hnt
  rw [Ideal.map_span, Set.image_singleton, Ideal.span_singleton_le_iff_mem] at hle
  simpa using hle

theorem QS_notMem (hE : H.toHostRaw.Exact) (P : HeightOneSpectrum (𝓞 H.E)) {p : ℕ} (hp : p.Prime)
    (hc : Nat.card (𝓞 H.E ⧸ P.asIdeal) = p) (h2 : (p : 𝓞 H.E) ∉ P.asIdeal ^ 2) : (H.QS : 𝓞 H.E) ∉ P.asIdeal := by
  have hP := P.isPrime
  have hpm : (p : 𝓞 H.E) ∈ P.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ← hc, ← nsmul_one]
    exact card_nsmul_eq_zero'
  intro hm
  by_cases hd : p ∣ H.QS
  · exact h2 (H.mem_sq_of_dvd_QS hE hp hd P.asIdeal hpm)
  · have hcop : IsCoprime ((p : ℕ) : 𝓞 H.E) ((H.QS : ℕ) : 𝓞 H.E) := ((Nat.Prime.coprime_iff_not_dvd hp).2 hd).cast
    obtain ⟨a, b, hab⟩ := hcop
    exact hP.ne_top ((Ideal.eq_top_iff_one _).2 (hab ▸ P.asIdeal.add_mem (P.asIdeal.mul_mem_left a hpm) (P.asIdeal.mul_mem_left b hm)))

theorem condN_mul_notMem (hE : H.toHostRaw.Exact) (P : HeightOneSpectrum (𝓞 H.E)) {p : ℕ} (hp : p.Prime)
    (hc : Nat.card (𝓞 H.E ⧸ P.asIdeal) = p) (h2 : (p : 𝓞 H.E) ∉ P.asIdeal ^ 2) {T : ℕ}
    (h : ((2 * H.q * H.d * T : ℕ) : 𝓞 H.E) ∉ P.asIdeal) : ((H.condN * T : ℕ) : 𝓞 H.E) ∉ P.asIdeal := by
  intro hm
  have e : ((H.condN * T : ℕ) : 𝓞 H.E) = (H.QS : 𝓞 H.E) * ((H.q * H.d * T : ℕ) : 𝓞 H.E) := by
    simp only [HostRaw.condN]; push_cast; ring
  rw [e] at hm
  rcases P.isPrime.mem_or_mem hm with h1 | h1
  · exact H.QS_notMem hE P hp hc h2 h1
  · refine h ?_
    have e' : ((2 * H.q * H.d * T : ℕ) : 𝓞 H.E) = 2 * ((H.q * H.d * T : ℕ) : 𝓞 H.E) := by push_cast; ring
    rw [e']
    exact P.asIdeal.mul_mem_left _ h1

theorem two_mul_notMem_of_condN (P : HeightOneSpectrum (𝓞 H.E)) {T : ℕ}
    (h : ((H.condN * T : ℕ) : 𝓞 H.E) ∉ P.asIdeal) : ((2 * H.q * H.d * T : ℕ) : 𝓞 H.E) ∉ P.asIdeal := by
  intro hm
  obtain ⟨c, hc⟩ := H.two_dvd_QS
  refine h ?_
  have e : ((H.condN * T : ℕ) : 𝓞 H.E) = (c : 𝓞 H.E) * ((2 * H.q * H.d * T : ℕ) : 𝓞 H.E) := by
    simp only [HostRaw.condN]; rw [hc]; push_cast; ring
  rw [e]
  exact P.asIdeal.mul_mem_left _ hm

end Formalism.HC.HostAx

end
