import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.IsAdmissiblePrimeListNil
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChebotarevDegreeOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChebotarevDegreeOneIffCheb

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

theorem UpperTheory.V.ML.chebQ :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (V : Set (G ℚ Ω)), IsOpen V → V.Nonempty → ∀ T : ℕ, T ≠ 0 → ∃ (q : ℕ) (A : ValuationSubring Ω) (φ : G ℚ Ω), q.Prime ∧ ¬ q ∣ T ∧ Over A q ∧ IsFrob (F := ℚ) A q φ ∧ φ ∈ V := by
  intro Ω _ _ _ V hV hne T hT
  let S : Set (HeightOneSpectrum (𝓞 ℚ)) := {v | v.asIdeal ∣ Ideal.span {(T : 𝓞 ℚ)}}
  have hS : S.Finite := Ideal.finite_factors (by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hT)
  have hD := GlobalTheory.Published.ChebotarevDegreeOne.dense (F := ℚ) (Ω := Ω) GlobalTheory.Published.chebotarevDegreeOne' hS
  obtain ⟨φ, hφV, v, hvS, hv1, B, hB, hF⟩ := hD.inter_open_nonempty V hV hne
  have hq : normV v = Ideal.absNorm v.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rfl
  have hprime : (normV v).Prime := by
    rw [hq]
    exact ((GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified ℚ).1 v).2 hv1
  have hmem : ((normV v : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := by
    rw [hq]
    exact Ideal.absNorm_mem _
  refine ⟨normV v, B, φ, hprime, ?_, ?_, hF, hφV⟩
  · intro hdvd
    apply hvS
    show v.asIdeal ∣ Ideal.span {(T : 𝓞 ℚ)}
    rw [Ideal.dvd_span_singleton]
    obtain ⟨c, hc⟩ := hdvd
    rw [hc, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ hmem
  · show B.valuation ((normV v : ℕ) : Ω) < 1
    have := (hB ((normV v : ℕ) : 𝓞 ℚ)).2 hmem
    simpa using this
