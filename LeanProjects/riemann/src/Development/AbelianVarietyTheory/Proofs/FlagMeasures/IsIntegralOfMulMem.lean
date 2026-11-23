import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.IdealsOfNormEqIndexSet
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical nonZeroDivisors

noncomputable section

namespace GlobalTheory.DegCnt.NormOneCount

theorem le_totient_sq (n : ℕ) : n ≤ 2 * n.totient ^ 2 ∧ (Odd n → n ≤ n.totient ^ 2) := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
    obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [Nat.totient_prime_pow_succ hp]
    have h2 := hp.two_le
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    have hq : 1 ≤ q := by omega
    have hP : 1 ≤ (q + 1) ^ k := Nat.one_le_pow _ _ (by omega)
    rw [pow_succ, Nat.add_sub_cancel]
    generalize (q + 1) ^ k = P at hP ⊢
    have hPP : P ≤ P ^ 2 := by nlinarith
    refine ⟨?_, fun ho => ?_⟩
    · have h1 : q + 1 ≤ 2 * q ^ 2 := by nlinarith
      calc P * (q + 1) ≤ P ^ 2 * (2 * q ^ 2) := Nat.mul_le_mul hPP h1
        _ = _ := by ring
    · have ho' : Odd (q + 1) := (Nat.odd_mul.1 ho).2
      have hq2 : 2 ≤ q := by
        obtain ⟨m, hm⟩ := ho'
        omega
      have h1 : q + 1 ≤ q ^ 2 := by nlinarith
      calc P * (q + 1) ≤ P ^ 2 * q ^ 2 := Nat.mul_le_mul hPP h1
        _ = _ := by ring
  | zero => simp
  | one => simp
  | coprime a b ha hb hab iha ihb =>
    rw [Nat.totient_mul hab]
    refine ⟨?_, fun ho => ?_⟩
    · rcases Nat.even_or_odd a with hea | hoa
      · have hob : Odd b := by
          rcases Nat.even_or_odd b with heb | hob
          · have := Nat.dvd_gcd hea.two_dvd heb.two_dvd
            rw [hab.gcd_eq_one] at this
            omega
          · exact hob
        calc a * b ≤ (2 * a.totient ^ 2) * b.totient ^ 2 := Nat.mul_le_mul iha.1 (ihb.2 hob)
          _ = _ := by ring
      · calc a * b ≤ a.totient ^ 2 * (2 * b.totient ^ 2) := Nat.mul_le_mul (iha.2 hoa) ihb.1
          _ = _ := by ring
    · obtain ⟨h1, h2⟩ := Nat.odd_mul.1 ho
      calc a * b ≤ a.totient ^ 2 * b.totient ^ 2 := Nat.mul_le_mul (iha.2 h1) (ihb.2 h2)
        _ = _ := by ring

theorem card_torsion_le (K : Type) [Field K] [NumberField K] :
    Nat.card (Units.torsion K) ≤ 2 * Module.finrank ℚ K ^ 2 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Units.torsion K)
  have h1 : IsPrimitiveRoot g (Nat.card (Units.torsion K)) := hg ▸ IsPrimitiveRoot.orderOf g
  have h2 : IsPrimitiveRoot (g : (𝓞 K)ˣ) (Nat.card (Units.torsion K)) :=
    h1.map_of_injective (f := (Units.torsion K).subtype) Subtype.val_injective
  have h3 : IsPrimitiveRoot ((g : (𝓞 K)ˣ) : 𝓞 K) (Nat.card (Units.torsion K)) :=
    IsPrimitiveRoot.coe_units_iff.2 h2
  have h4 : IsPrimitiveRoot (algebraMap (𝓞 K) K ((g : (𝓞 K)ˣ) : 𝓞 K)) (Nat.card (Units.torsion K)) :=
    h3.map_of_injective (RingOfIntegers.coe_injective)
  have hpos : 0 < Nat.card (Units.torsion K) := Nat.card_pos
  have h5 := IsPrimitiveRoot.lcm_totient_le_finrank (K := ℚ) h4 h4
    (by rw [Nat.lcm_self]; exact Polynomial.cyclotomic.irreducible_rat hpos)
  rw [Nat.lcm_self] at h5
  exact (le_totient_sq _).1.trans (by gcongr)

variable {K : Type} [Field K] [NumberField K]

theorem isIntegral_of_mul_mem {𝔞 : Ideal (𝓞 K)} (h : 𝔞 ≠ ⊥) {u : K}
    (hu : ∀ t ∈ ipow 𝔞 1, u * t ∈ ipow 𝔞 1) : IsIntegral ℤ u := by
  have hne : ipow 𝔞 1 ≠ ⊥ := by
    unfold ipow
    rw [zpow_one]
    intro h0
    exact (FractionalIdeal.coeIdeal_ne_zero.2 h) (FractionalIdeal.coeToSubmodule_eq_bot.1 h0)
  have hfg : (ipow 𝔞 1).FG := by
    unfold ipow
    exact FractionalIdeal.fg_of_isNoetherianRing le_rfl _
  have h1 : IsIntegral (𝓞 K) u :=
    isIntegral_of_smul_mem_submodule (ipow 𝔞 1) hne hfg u (fun t ht => by simpa using hu t ht)
  exact isIntegral_trans u h1

theorem exists_torsion [StarRing K] (hK : ∀ (φ : K →+* ℂ) (a : K), φ (star a) = starRingEnd ℂ (φ a))
    {𝔞 𝔞' : Ideal (𝓞 K)} (h : 𝔞' ≠ ⊥) {c d : K} (hc : c * star c = 1) (hd : d * star d = 1)
    (h1 : ∀ t : K, t * c ∈ ipow 𝔞 1 ↔ t ∈ ipow 𝔞' 1) (h2 : ∀ t : K, t * d ∈ ipow 𝔞 1 ↔ t ∈ ipow 𝔞' 1) :
    ∃ ζ : Units.torsion K, c = algebraMap (𝓞 K) K ((ζ : (𝓞 K)ˣ) : 𝓞 K) * d := by
  have hc0 : c ≠ 0 := left_ne_zero_of_mul_eq_one hc
  have hd0 : d ≠ 0 := left_ne_zero_of_mul_eq_one hd
  have i1 : IsIntegral ℤ (c / d) := isIntegral_of_mul_mem h fun t ht => by
    rw [← h2, show c / d * t * d = t * c by field_simp, h1]; exact ht
  have i2 : IsIntegral ℤ (d / c) := isIntegral_of_mul_mem h fun t ht => by
    rw [← h1, show d / c * t * c = t * d by field_simp, h2]; exact ht
  obtain ⟨a, ha⟩ : ∃ a : 𝓞 K, algebraMap (𝓞 K) K a = c / d := ⟨⟨c / d, i1⟩, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : 𝓞 K, algebraMap (𝓞 K) K b = d / c := ⟨⟨d / c, i2⟩, rfl⟩
  have hm : a * b = 1 := by
    apply RingOfIntegers.coe_injective
    rw [map_mul, map_one, ha, hb]
    field_simp
  have hn : ∀ (φ : K →+* ℂ) (e : K), e * star e = 1 → ‖φ e‖ = 1 := fun φ e he => by
    have h3 := congrArg (fun z => ‖φ z‖) he
    simp only [map_mul, hK, map_one, norm_mul, norm_one, RCLike.norm_conj] at h3
    nlinarith [norm_nonneg (φ e)]
  refine ⟨⟨Units.mkOfMulEqOne _ _ hm, (Units.mem_torsion K).2 fun w => ?_⟩, ?_⟩
  · show w (algebraMap (𝓞 K) K a) = 1
    rw [ha, ← InfinitePlace.norm_embedding_eq, map_div₀, norm_div, hn _ c hc, hn _ d hd, div_one]
  · show c = algebraMap (𝓞 K) K a * d
    rw [ha]
    field_simp

theorem main : ∀ (K : Type) [Field K] [NumberField K] [StarRing K], Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ x : ℝ, 1 ≤ x → ((({c : K | c * star c = 1 ∧ ∃ 𝔞 𝔞' : Ideal (𝓞 K), 𝔞 ≠ ⊥ ∧ 𝔞' ≠ ⊥ ∧ (Ideal.absNorm 𝔞 : ℝ) ≤ x ∧ (Ideal.absNorm 𝔞' : ℝ) ≤ x ∧ ∀ t : K, t * c ∈ ipow 𝔞 1 ↔ t ∈ ipow 𝔞' 1}).encard : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal (8 * ((Formalism.HermitianLatticesTheory.fDeg K) : ℝ) ^ 2 * x ^ (2 * (2 + cf K))) := by
  intro K _ _ _ hK x hx
  obtain ⟨hfin, hle⟩ := Formalism.HermitianLatticeCounting.P.ideal_norm_le_count K x hx
  set A := {I : Ideal (𝓞 K) | I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ x} with hA
  let c0 : Ideal (𝓞 K) × Ideal (𝓞 K) → K := fun p =>
    if h : ∃ d : K, d * star d = 1 ∧ ∀ t : K, t * d ∈ ipow p.1 1 ↔ t ∈ ipow p.2 1 then h.choose else 0
  let g : (Ideal (𝓞 K) × Ideal (𝓞 K)) × Units.torsion K → K := fun q =>
    algebraMap (𝓞 K) K ((q.2 : (𝓞 K)ˣ) : 𝓞 K) * c0 q.1
  have hB : ((A ×ˢ A) ×ˢ (Set.univ : Set (Units.torsion K))).Finite :=
    (hfin.prod hfin).prod Set.finite_univ
  have hsub : {c : K | c * star c = 1 ∧ ∃ 𝔞 𝔞' : Ideal (𝓞 K), 𝔞 ≠ ⊥ ∧ 𝔞' ≠ ⊥ ∧ (Ideal.absNorm 𝔞 : ℝ) ≤ x ∧
      (Ideal.absNorm 𝔞' : ℝ) ≤ x ∧ ∀ t : K, t * c ∈ ipow 𝔞 1 ↔ t ∈ ipow 𝔞' 1} ⊆
      g '' ((A ×ˢ A) ×ˢ (Set.univ : Set (Units.torsion K))) := by
    rintro c ⟨hc, 𝔞, 𝔞', h1, h2, h3, h4, h5⟩
    have hex : ∃ d : K, d * star d = 1 ∧ ∀ t : K, t * d ∈ ipow 𝔞 1 ↔ t ∈ ipow 𝔞' 1 := ⟨c, hc, h5⟩
    obtain ⟨ζ, hζ⟩ := exists_torsion hK.2.1 h2 hc hex.choose_spec.1 h5 hex.choose_spec.2
    refine ⟨((𝔞, 𝔞'), ζ), ⟨⟨⟨h1, h3⟩, ⟨h2, h4⟩⟩, trivial⟩, ?_⟩
    simp only [g, c0, dif_pos hex]
    exact hζ.symm
  have henc := (Set.encard_le_encard hsub).trans (Set.encard_image_le _ _)
  rw [← hB.cast_ncard_eq, Set.ncard_prod, Set.ncard_prod, Set.ncard_univ] at henc
  refine (ENat.toENNReal_le.2 henc).trans ?_
  rw [ENat.toENNReal_coe, ← ENNReal.ofReal_natCast]
  apply ENNReal.ofReal_le_ofReal
  have hd : Module.finrank ℚ K = 2 * Formalism.HermitianLatticesTheory.fDeg K := by
    have := hK.1
    rw [IsTotallyComplex.finrank, Formalism.HermitianLatticesTheory.fDeg, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      IsTotallyComplex.nrRealPlaces_eq_zero, zero_add]
  have hw : (Nat.card (Units.torsion K) : ℝ) ≤ 8 * ((Formalism.HermitianLatticesTheory.fDeg K) : ℝ) ^ 2 := by
    have h1 := card_torsion_le K
    rw [hd] at h1
    have h2 : (Nat.card (Units.torsion K) : ℝ) ≤ 2 * (2 * (Formalism.HermitianLatticesTheory.fDeg K : ℝ)) ^ 2 := by
      exact_mod_cast h1
    linarith
  have hA' : (A.ncard : ℝ) ≤ x ^ (2 + cf K) :=
    hle.trans (Real.rpow_le_rpow_of_exponent_le hx (by unfold cf; linarith))
  have hx0 : 0 < x := by linarith
  push_cast
  calc (A.ncard : ℝ) * A.ncard * Nat.card (Units.torsion K)
      ≤ x ^ (2 + cf K) * x ^ (2 + cf K) * (8 * ((Formalism.HermitianLatticesTheory.fDeg K) : ℝ) ^ 2) := by gcongr
    _ = _ := by rw [← Real.rpow_add hx0, two_mul (2 + cf K)]; ring

end GlobalTheory.DegCnt.NormOneCount
