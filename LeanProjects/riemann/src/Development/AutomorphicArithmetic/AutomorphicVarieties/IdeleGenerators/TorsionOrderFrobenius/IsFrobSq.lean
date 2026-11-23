import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShapeFacts
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Places
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal UpperTheory.V.Base

private theorem pow_cong {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {a b : Ω} (ha : A.valuation a ≤ 1)
    (hb : A.valuation b ≤ 1) (h : A.valuation (a - b) < 1) (m : ℕ) : A.valuation (a ^ m - b ^ m) < 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show a ^ (m + 1) - b ^ (m + 1) = a ^ m * (a - b) + (a ^ m - b ^ m) * b by ring]
    refine Valuation.map_add_lt _ ?_ ?_
    · rw [map_mul, map_pow]
      exact lt_of_le_of_lt (mul_le_of_le_one_left' (pow_le_one' ha m)) h
    · rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_right' hb) ih

private theorem isFrob_sq {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] {A : ValuationSubring Ω}
    {q : ℕ} {g : G k Ω} (hg : IsFrob (F := k) A q g) : IsFrob (F := k) A (q ^ 2) (g * g) := by
  refine ⟨Subgroup.mul_mem _ hg.1 hg.1, fun x hx => ?_⟩
  have hgx : A.valuation (g x) ≤ 1 :=
    (A.valuation_le_one_iff _).2 ((apply_mem_iff_of_mem_Dec (F := k) hg.1 x).2 ((A.valuation_le_one_iff _).1 hx))
  have h1 := hg.2 _ hgx
  have h2 := pow_cong A hgx (b := x ^ q) (by rw [map_pow]; exact pow_le_one' hx _) (hg.2 x hx) q
  have h3 := Valuation.map_add_lt A.valuation h1 h2
  rw [sub_add_sub_cancel, ← pow_mul, ← sq] at h3
  rw [AlgEquiv.mul_apply]
  exact h3

theorem UpperTheory.V.Sd.Tw.inert :
    ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Algebra K Ω],
        Module.finrank ℚ K = 2 → ∀ (p : ℕ), p.Prime → ∀ (A : ValuationSubring Ω), A.valuation (p : Ω) < 1 →
        Ine (F := ℚ) A ≤ galOf ℚ K Ω → ∀ t : G ℚ Ω, IsFrob (F := ℚ) A p t → t ∉ galOf ℚ K Ω →
        ∃ w : HeightOneSpectrum (𝓞 K), IsPlaceOver A w ∧ w.asIdeal = Ideal.span {(p : 𝓞 K)} ∧
          ∀ s : G K Ω, galEmb ℚ K Ω s = t * t → IsFrob (F := K) A (normV w) s := by
  intro K Ω _ _ _ _ _ _ hK p hp A hA hI t ht htK
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  haveI : IsAlgClosure K Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) K⟩
  obtain ⟨h1, h2, h3, -⟩ := UpperTheory.V.Base.places K Ω p A
  obtain ⟨w, hw⟩ := h1 fun h => (h2 h).2 hA
  have hpw : (p : 𝓞 K) ∈ w.asIdeal := (h3 w hw).1 hA
  have hle : Ideal.span {(p : 𝓞 K)} ≤ w.asIdeal := (Ideal.span_singleton_le_iff_mem _).2 hpw
  have hN : Ideal.absNorm (Ideal.span {(p : 𝓞 K)}) = p ^ 2 := by
    rw [Ideal.absNorm_span_natCast, NumberField.RingOfIntegers.rank, hK]
  have hn : normV w = Ideal.absNorm w.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl
  have hq : normV w = p ^ 2 := by
    obtain ⟨j, hj, e⟩ := (Nat.dvd_prime_pow hp).1 (hN ▸ Ideal.absNorm_dvd_absNorm_of_le hle)
    interval_cases j
    · exact absurd (Ideal.absNorm_eq_one_iff.1 (by simpa using e)) w.isPrime.ne_top
    · exfalso
      obtain ⟨φ, hφ⟩ := ReciprocityTheory.Gal.exists_isFrob hw
      rw [hn, e, pow_one] at hφ
      have hφ' : IsFrob (F := ℚ) A p (galEmb ℚ K Ω φ) := ⟨hφ.1, hφ.2⟩
      have h := hI (inv_mul_mem_Ine_of_isFrob hφ' ht)
      exact htK (by simpa using (galOf ℚ K Ω).mul_mem (galEmb_mem ℚ K Ω φ) h)
    · rw [hn, e]
  refine ⟨w, hw, ?_, fun s hs => ?_⟩
  · obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.2 hle
    have e := congrArg Ideal.absNorm hJ
    rw [map_mul, hN, ← hn, hq] at e
    have hJ1 : Ideal.absNorm J = 1 := by
      have := pow_pos hp.pos 2
      exact (Nat.mul_eq_left this.ne').1 e.symm
    rw [hJ, Ideal.absNorm_eq_one_iff.1 hJ1, Ideal.mul_top]
  · have h := isFrob_sq ht
    rw [← hs, ← hq] at h
    exact ⟨h.1, h.2⟩
