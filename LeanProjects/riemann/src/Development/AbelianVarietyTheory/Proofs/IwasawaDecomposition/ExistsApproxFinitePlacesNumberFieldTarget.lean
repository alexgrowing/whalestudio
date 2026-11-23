import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocUnitApply
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.NormCompat

noncomputable section

namespace GlobalTheory.FinPlaceApprox

theorem exists_approx_finite_places (F : Type) [Field F] [NumberField F]
    (T : Finset (HeightOneSpectrum (𝓞 F))) (t : HeightOneSpectrum (𝓞 F) → F) (M : ℕ) :
    ∃ a : F, ∀ v ∈ T, v.valuation F (a - t v) ≤ WithZero.exp (-(M : ℤ)) := by
  classical
  obtain ⟨⟨d, hd⟩, hdS⟩ :=
    IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 F)) (T.image t)
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  have hn : ∀ v ∈ T, ∃ n : 𝓞 F, algebraMap (𝓞 F) F n = algebraMap (𝓞 F) F d * t v := by
    intro v hv
    obtain ⟨n, hn⟩ := hdS (t v) (Finset.mem_image_of_mem t hv)
    exact ⟨n, by rw [hn, Algebra.smul_def]⟩
  choose! n hn using hn
  have h0 : ∀ v : HeightOneSpectrum (𝓞 F), v.intValuation d ≠ 0 := fun v => v.intValuation_ne_zero d hd0
  obtain ⟨x, hx⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := T) (fun v => v.asIdeal)
    (fun v => M + ((v.intValuation d).log).natAbs) (fun v _ => v.prime)
    (fun v _ w _ h h' => h (HeightOneSpectrum.ext h')) (fun v => n v.1)
  have dE : algebraMap (𝓞 F) F d ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 hd0
  refine ⟨algebraMap (𝓞 F) F x / algebraMap (𝓞 F) F d, fun v hv => ?_⟩
  have hxv : x - n v ∈ v.asIdeal ^ (M + ((v.intValuation d).log).natAbs) := hx v hv
  have key : algebraMap (𝓞 F) F x / algebraMap (𝓞 F) F d - t v =
      algebraMap (𝓞 F) F (x - n v) / algebraMap (𝓞 F) F d := by
    rw [map_sub, hn v hv]; field_simp
  rw [key, map_div₀, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
    div_le_iff₀ (zero_lt_iff.2 (h0 v))]
  refine ((v.intValuation_le_pow_iff_mem _ _).2 hxv).trans ?_
  have hle : (v.intValuation d).log ≤ 0 := by
    have := v.intValuation_le_one d
    rw [← WithZero.exp_log (h0 v), ← WithZero.exp_zero, WithZero.exp_le_exp] at this
    exact this
  conv_rhs => rw [← WithZero.exp_log (h0 v)]
  rw [← WithZero.exp_add, WithZero.exp_le_exp]
  omega

theorem approx_target : ∀ (F : Type) [Field F] [NumberField F] (T : Finset (HeightOneSpectrum (𝓞 F)))
    (t : HeightOneSpectrum (𝓞 F) → F) (M : ℕ),
    ∃ a : F, ∀ v ∈ T, v.valuation F (a - t v) ≤ WithZero.exp (-(M : ℤ)) :=
  fun F _ _ T t M => exists_approx_finite_places F T t M

end GlobalTheory.FinPlaceApprox
