import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.ExistsIdempotentHeckeOperatorWithRegularSupportAlt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.NsmulIntegIff
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc comp)
open UpperTheory.Gal.W2.Seed UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl

private theorem val_natCast_lt_one {E : Type} [Field E] [NumberField E] (u : Plc E) (r : ℕ)
    (hu : (r : 𝓞 E) ∈ u.asIdeal) : Valued.v (r : u.adicCompletion E) < 1 := by
  have h := (u.valuation_lt_one_iff_mem (K := E) (r : 𝓞 E)).2 hu
  have e : ((r : ℕ) : u.adicCompletion E) = algebraMap E (u.adicCompletion E) (r : E) :=
    (map_natCast _ r).symm
  have e2 : Valued.v (algebraMap E (u.adicCompletion E) (r : E)) = u.valuation E (r : E) :=
    IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' u _
  rw [e, e2]
  simpa using h

private theorem eventually_integral {E : Type} [Field E] [NumberField E] (u : Plc E) (r : ℕ)
    (hu : (r : 𝓞 E) ∈ u.asIdeal) (x : u.adicCompletion E) :
    ∀ᶠ M : ℕ in Filter.atTop, ((r ^ M : ℕ) : u.adicCompletion E) * x ∈ u.adicCompletionIntegers E := by
  have h1 := val_natCast_lt_one u r hu
  by_cases hx : x = 0
  · simp [hx]
  have hv : Valued.v x ≠ 0 := by simpa using hx
  obtain ⟨M₀, hM₀⟩ := exists_pow_lt₀ h1 (Units.mk0 _ (inv_ne_zero hv))
  filter_upwards [Filter.eventually_ge_atTop M₀] with M hM
  rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, Nat.cast_pow, map_pow]
  have h2 : Valued.v (r : u.adicCompletion E) ^ M ≤ (Valued.v x)⁻¹ :=
    (pow_le_pow_of_le_one zero_le' h1.le hM).trans hM₀.le
  calc _ ≤ (Valued.v x)⁻¹ * Valued.v x := mul_le_mul' h2 le_rfl
    _ = 1 := inv_mul_cancel₀ hv

theorem UpperTheory.exists_primePow_scalar_integral_of_good_prime :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p) (F : Frame S) (r : ℕ), r.Prime → A.Good r → ∀ g : GUf E n, (∀ u : Plc E, (r : 𝓞 E) ∉ u.asIdeal → comp u g = 1) → ∃ M : ℕ, ∀ d : GUf E n, (∀ w : Plc E, (comp w d).val = ((r ^ M : ℕ) : w.adicCompletion E) • (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E))) → Integ S.L (F.j (g * d)) := by
  intro E _ _ _ A n p _ S F r hr _ g hg
  have hr0 : (r : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.2 hr.ne_zero
  have hT : {u : Plc E | (r : 𝓞 E) ∈ u.asIdeal}.Finite := by
    refine (Ideal.finite_factors (I := Ideal.span {(r : 𝓞 E)}) (by simpa using hr0)).subset fun u hu => ?_
    exact Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hu)
  have hev : ∀ᶠ M : ℕ in Filter.atTop, ∀ u ∈ {u : Plc E | (r : 𝓞 E) ∈ u.asIdeal}, ∀ i k,
      ((r ^ M : ℕ) : u.adicCompletion E) * F.cmp u g i k ∈ u.adicCompletionIntegers E := by
    rw [Filter.eventually_all_finite hT]
    intro u hu
    rw [Filter.eventually_all]
    intro i
    rw [Filter.eventually_all]
    intro k
    exact eventually_integral u r hu _
  obtain ⟨M, hM⟩ := hev.exists
  refine ⟨M, fun d hd => (integ_iff F _).2 fun w _ i k => ?_⟩
  have e : F.cmp w (g * d) = ((r ^ M : ℕ) : w.adicCompletion E) • F.cmp w g := by
    unfold Frame.cmp
    simp only [map_mul, Units.val_mul, hd w]
    simp [Matrix.mul_assoc]
  rw [e, Matrix.smul_apply, smul_eq_mul]
  by_cases hw : (r : 𝓞 E) ∈ w.asIdeal
  · exact hM w hw i k
  · have h1 : F.cmp w g = 1 := by
      unfold Frame.cmp
      simp [hg w hw]
    rw [h1, Matrix.one_apply]
    split_ifs
    · simpa using natCast_mem (w.adicCompletionIntegers E) (r ^ M)
    · simp
