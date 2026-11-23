import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.ExistsIdempotentHeckeOperatorWithRegularSupportAlt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.PDatEx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PPerfCof
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsPlace

open NumberField IsDedekindDomain UpperTheory.Gal.W2.Seed UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.CertificateRingHomMap (Plc)

namespace UpperTheory.Gal.Spc.EntrywiseClass

private theorem exists_root (tr nm : ℤ) (h : tr ^ 2 - 4 * nm < 0) (b : ℕ) :
    ∃ q : ℕ, q.Prime ∧ b < q ∧ ∃ r : ℤ, (q : ℤ) ∣ r ^ 2 - tr * r + nm := by
  have hnm : 0 < nm := by nlinarith [sq_nonneg tr]
  set c : ℕ := (b + tr.natAbs + 1).factorial with hc
  have hcge : b + tr.natAbs + 1 ≤ c := Nat.self_le_factorial _
  have hcZ : (tr.natAbs : ℤ) + 1 ≤ (c : ℤ) := by omega
  have htr : tr ≤ tr.natAbs := by omega
  set g : ℤ := nm * (c : ℤ) ^ 2 - tr * c + 1 with hg
  have hcpos : (0 : ℤ) < c := by omega
  have hg1 : 1 < g := by
    have h1 : (c : ℤ) ≤ nm * c := by nlinarith
    have h2 : 0 < nm * c - tr := by omega
    have : 0 < (c : ℤ) * (nm * c - tr) := mul_pos hcpos h2
    rw [hg]; nlinarith
  have hne : g.natAbs ≠ 1 := by omega
  refine ⟨g.natAbs.minFac, Nat.minFac_prime hne, ?_, nm * c, ?_⟩
  · by_contra hle
    have hq := Nat.minFac_prime hne
    have hqc : g.natAbs.minFac ∣ c := (hq.dvd_factorial).2 (by omega)
    have hqg : (g.natAbs.minFac : ℤ) ∣ g := Int.natCast_dvd.2 (Nat.minFac_dvd _)
    have hqc' : (g.natAbs.minFac : ℤ) ∣ (c : ℤ) := by exact_mod_cast hqc
    have h1 : (g.natAbs.minFac : ℤ) ∣ 1 := by
      have e : (1 : ℤ) = g - c * (nm * c - tr) := by rw [hg]; ring
      rw [e]; exact dvd_sub hqg (Dvd.dvd.mul_right hqc' _)
    have := Int.eq_one_of_dvd_one (by omega) h1
    have h2 := hq.one_lt
    omega
  · have hqg : (g.natAbs.minFac : ℤ) ∣ g := Int.natCast_dvd.2 (Nat.minFac_dvd _)
    have e : (nm * c) ^ 2 - tr * (nm * c) + nm = nm * g := by rw [hg]; ring
    rw [e]; exact Dvd.dvd.mul_left hqg _

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

private theorem not_both (u : Plc E) {a b : ℕ} (h : a.Coprime b) (ha : (a : 𝓞 E) ∈ u.asIdeal) (hb : (b : 𝓞 E) ∈ u.asIdeal) : False := by
  obtain ⟨s, t, hst⟩ := Nat.isCoprime_iff_coprime.2 h
  have e : (1 : 𝓞 E) = (s : 𝓞 E) * (a : 𝓞 E) + (t : 𝓞 E) * (b : 𝓞 E) := by
    exact_mod_cast (congrArg (Int.cast : ℤ → 𝓞 E) hst).symm
  refine u.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
  rw [e]
  exact u.asIdeal.add_mem (u.asIdeal.mul_mem_left _ ha) (u.asIdeal.mul_mem_left _ hb)

private theorem exists_place (q : ℕ) (hq : q.Prime) : ∃ w : Plc E, (q : 𝓞 E) ∈ w.asIdeal :=
  _root_.UpperTheory.Reformulated.B.ExistsPlace.exists_place q hq

private theorem finite_above (q : ℕ) (hq : q.Prime) : {w : Plc E | (q : 𝓞 E) ∈ w.asIdeal}.Finite := by
  have hq0 : (q : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.2 hq.ne_zero
  refine (Ideal.finite_factors (I := Ideal.span {(q : 𝓞 E)}) (by simpa using hq0)).subset fun w hw => ?_
  exact Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hw)

private theorem cj_cj (A : Arith E) (u : Plc E) : CertificateRingHomMap.cj (CertificateRingHomMap.cj u) = u := by
  apply HeightOneSpectrum.ext
  ext y
  rw [UpperTheory.Gal.G1.pCjMem E A, UpperTheory.Gal.G1.pCjMem E A, A.bar_bar]

private theorem eq_or_cj (A : Arith E) (w u : Plc E)
    (h : w.under (𝓞 (maximalRealSubfield E)) = u.under (𝓞 (maximalRealSubfield E))) : u = w ∨ u = CertificateRingHomMap.cj w := by
  have hsub : (u.asIdeal : Set (𝓞 E)) ⊆ (w.asIdeal : Set (𝓞 E)) ∪ ((CertificateRingHomMap.cj w).asIdeal : Set (𝓞 E)) := by
    intro y hy
    have hy' : y ∈ u.asIdeal := hy
    have ht : IsCMField.complexConj E ((y * A.bar y : 𝓞 E) : E) = ((y * A.bar y : 𝓞 E) : E) := by
      rw [← A.bar_eq, map_mul, A.bar_bar, mul_comm]
    have hmem : ((y * A.bar y : 𝓞 E) : E) ∈ maximalRealSubfield E := (IsCMField.complexConj_eq_self_iff E _).1 ht
    have hint : IsIntegral ℤ (⟨_, hmem⟩ : maximalRealSubfield E) :=
      (isIntegral_algebraMap_iff (A := maximalRealSubfield E) (B := E) (algebraMap (maximalRealSubfield E) E).injective).1
        (RingOfIntegers.isIntegral_coe (y * A.bar y))
    let z : 𝓞 (maximalRealSubfield E) := ⟨⟨_, hmem⟩, hint⟩
    have hz : algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) z = y * A.bar y := RingOfIntegers.ext rfl
    have h1 : z ∈ (u.under (𝓞 (maximalRealSubfield E))).asIdeal := by
      rw [HeightOneSpectrum.under_asIdeal, Ideal.under_def, Ideal.mem_comap, hz]
      exact u.asIdeal.mul_mem_right _ hy'
    rw [← h, HeightOneSpectrum.under_asIdeal, Ideal.under_def, Ideal.mem_comap, hz] at h1
    rcases w.isPrime.mem_or_mem h1 with h2 | h2
    · exact Or.inl h2
    · exact Or.inr ((UpperTheory.Gal.G1.pCjMem E A w y).2 h2)
  rcases Ideal.subset_union.1 hsub with h1 | h1
  · exact Or.inl (HeightOneSpectrum.ext (u.isMaximal.eq_of_le w.isPrime.ne_top h1))
  · exact Or.inr (HeightOneSpectrum.ext (u.isMaximal.eq_of_le (CertificateRingHomMap.cj w).isPrime.ne_top h1))

end UpperTheory.Gal.Spc.EntrywiseClass

theorem UpperTheory.Gal.Spc.auxiliary_prime_holds :
    UpperTheory.Gal.Spc.AuxiliaryInertOddPrime := by
  intro E _ _ _ A n p _ S x U w₀ Up V hG X
  obtain ⟨e, he, hperf⟩ := pPerfCof E A
  obtain ⟨q, hq, hb, r, hr⟩ := UpperTheory.Gal.Spc.EntrywiseClass.exists_root A.tr A.nm A.disc_neg
    (X.sup id + p + e + (A.tr ^ 2 - 4 * A.nm).natAbs + V.S.sup fun u => Ideal.absNorm u.asIdeal)
  have hX : q ∉ X := fun h => by
    have h1 := Finset.le_sup (f := id) h
    simp only [id] at h1
    omega
  have hqp : q ≠ p := by omega
  have hcop : ∀ a : ℕ, 0 < a → a < q → a.Coprime q := fun a h0 h1 =>
    ((Nat.Prime.coprime_iff_not_dvd hq).2 fun h => absurd (Nat.le_of_dvd h0 h) (by omega)).symm
  have hD : ¬ (q : ℤ) ∣ A.tr ^ 2 - 4 * A.nm := fun h => by
    have h1 : q ∣ (A.tr ^ 2 - 4 * A.nm).natAbs := Int.natCast_dvd.1 h
    have h2 : 0 < (A.tr ^ 2 - 4 * A.nm).natAbs := by have := A.disc_neg; omega
    have := Nat.le_of_dvd h2 h1
    omega
  have hs : A.SplitK q := ⟨hD, r, hr⟩
  have hgood : A.Good q := ⟨hs, hperf q (hcop e he (by omega))⟩
  have hoff : ∀ u ∈ V.S, (q : 𝓞 E) ∉ u.asIdeal := fun u hu h => by
    have h1 : Ideal.absNorm u.asIdeal ≤ V.S.sup fun u => Ideal.absNorm u.asIdeal :=
      Finset.le_sup (f := fun u : Plc E => Ideal.absNorm u.asIdeal) hu
    have h2 : 0 < Ideal.absNorm u.asIdeal := Nat.pos_of_ne_zero fun h0 => u.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
    exact UpperTheory.Gal.Spc.EntrywiseClass.not_both u (hcop _ h2 (by omega)).symm h (Ideal.absNorm_mem u.asIdeal)
  obtain ⟨w₁, hw₁⟩ := UpperTheory.Gal.Spc.EntrywiseClass.exists_place (E := E) q hq
  have SD := fun (w : Plc E) (hw : (q : 𝓞 E) ∈ w.asIdeal) => Pl.sides_holds E A x hG q hq hs w hw
  obtain ⟨ρ, -, hρ⟩ := (SD w₁ hw₁).2.2.2.2.2.1
  have hiff := (SD w₁ hw₁).2.2.2.2.2.2 ρ hρ
  have hpo : ∀ u : Plc E, (q : 𝓞 E) ∈ u.asIdeal → (p : 𝓞 E) ∉ u.asIdeal := fun u hu hp =>
    UpperTheory.Gal.Spc.EntrywiseClass.not_both u ((Nat.coprime_primes hq (Fact.out : p.Prime)).2 hqp) hu hp
  have hT : {w : UpperTheory.Gal.Spc.Spl E p | (q : 𝓞 E) ∈ w.1.asIdeal ∧ A.ω - (ρ : 𝓞 E) ∈ w.1.asIdeal}.Finite :=
    ((UpperTheory.Gal.Spc.EntrywiseClass.finite_above (E := E) q hq).preimage (f := fun w : UpperTheory.Gal.Spc.Spl E p => w.1)
      (fun _ _ _ _ h => Subtype.ext h)).subset fun w hw => hw.1
  have hmk : ∀ u : Plc E, (q : 𝓞 E) ∈ u.asIdeal → A.ω - (ρ : 𝓞 E) ∈ u.asIdeal →
      ∃ w ∈ hT.toFinset, w.1 = u := fun u h1 h2 =>
    ⟨⟨u, (SD u h1).2.1, hpo u h1⟩, hT.mem_toFinset.2 ⟨h1, h2⟩, rfl⟩
  refine ⟨q, hT.toFinset, hX, hq, hqp, hgood, hoff, ⟨fun w hw => (hT.mem_toFinset.1 hw).1, fun u hu => ?_, fun w hw w' hw' hne heq => ?_⟩, ?_⟩
  · rcases (SD w₁ hw₁).2.2.1 u hu with h | h
    · obtain ⟨h1, h2⟩ := (hiff u).1 h
      obtain ⟨w, hw, e⟩ := hmk u h1 h2
      exact ⟨w, hw, Or.inl e⟩
    · obtain ⟨h1, h2⟩ := (hiff _).1 h
      obtain ⟨w, hw, e⟩ := hmk _ h1 h2
      exact ⟨w, hw, Or.inr (by rw [e]; exact UpperTheory.Gal.Spc.EntrywiseClass.cj_cj A u)⟩
  · have m := hT.mem_toFinset.1 hw
    have m' := hT.mem_toFinset.1 hw'
    rcases UpperTheory.Gal.Spc.EntrywiseClass.eq_or_cj A w.1 w'.1 heq with h | h
    · exact hne (Subtype.ext h.symm)
    · refine (SD w.1 m.1).1 (((SD w.1 m.1).2.2.2.2.2.2 ρ m.2 _).2 ?_)
      rw [← h]
      exact m'
  · obtain ⟨w, hw, -⟩ := hmk w₁ hw₁ hρ
    exact ⟨w, hw⟩
