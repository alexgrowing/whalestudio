import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.AdjointLowWeight.SymmetricCubeSymplecticSimilitude
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CoefSup
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ScNorm
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CoefficientsOfField

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3

private theorem int_of_norm {l : ℕ} [Fact l.Prime] (x : PadicAlgCl l) (h : ‖x‖ ≤ 1) : IsIntegral ℤ_[l] x := by
  have hi : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  have h0 : ‖x‖ = spectralValue (minpoly ℚ_[l] x) := rfl
  rw [h0, spectralValue_le_one_iff (minpoly.monic hi)] at h
  have hl' : minpoly ℚ_[l] x ∈ lifts (algebraMap ℤ_[l] ℚ_[l]) :=
    (lifts_iff_coeff_lifts _).mpr fun n => ⟨⟨_, h n⟩, rfl⟩
  obtain ⟨q, hq, -, hqm⟩ := lifts_and_degree_eq_and_monic hl' (minpoly.monic hi)
  exact ⟨q, hqm, by rw [← aeval_def, ← aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]⟩

private theorem coef_of_field {l : ℕ} [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K] :
    ∃ c : Coef l, ∀ x ∈ K, ‖x‖ ≤ 1 → x ∈ c.O :=
  _root_.UpperTheory.Reformulated.B.CoefficientsOfField.coef_of_field K

private theorem mem_pow_iff {l : ℕ} [Fact l.Prime] (c : Coef l) : ∃ a : ℝ, 0 < a ∧ a < 1 ∧
    ∀ (n : ℕ) (x : c.O), x ∈ maximalIdeal c.O ^ n ↔ ‖(x : PadicAlgCl l)‖ ≤ a ^ n := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible c.O
  have h1 : ‖(ϖ : PadicAlgCl l)‖ < 1 := (UpperTheory.V.Fr.sc_norm l c ϖ).2.1 hϖ.not_isUnit
  have h0 : 0 < ‖(ϖ : PadicAlgCl l)‖ := norm_pos_iff.2 fun h => hϖ.ne_zero (Subtype.ext h)
  refine ⟨_, h0, h1, fun n x => ?_⟩
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨y, rfl⟩
    rw [Subalgebra.coe_mul, Subalgebra.coe_pow, norm_mul, norm_pow]
    exact mul_le_of_le_one_right (by positivity) (UpperTheory.V.Fr.sc_norm l c y).1
  · intro hx
    rcases eq_or_ne x 0 with rfl | hx0
    · exact dvd_zero _
    obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hϖ
    have hu : ‖((u : c.O) : PadicAlgCl l)‖ = 1 :=
      le_antisymm (UpperTheory.V.Fr.sc_norm l c u).1 (not_lt.1 fun h => (UpperTheory.V.Fr.sc_norm l c u).2.2 h u.isUnit)
    rw [Subalgebra.coe_mul, Subalgebra.coe_pow, norm_mul, norm_pow, hu, one_mul] at hx
    exact (pow_dvd_pow ϖ ((pow_le_pow_iff_right_of_lt_one₀ h0 h1).1 hx)).mul_left _

theorem UpperTheory.integrality_of_norm_coefficients :
    UpperTheory.V.Sd.S3.CoefEx := by
  intro l _
  refine ⟨fun c E hE => ?_, fun c Γ _ f => ?_⟩
  · obtain ⟨c', hc'⟩ := coef_of_field E
    obtain ⟨c₁, h1, h2⟩ := (UpperTheory.V.HV.coefSup l).1 c c'
    exact ⟨c₁, h1, fun y hy h => h2 (hc' y hy h)⟩
  obtain ⟨a, h0, h1, ha⟩ := mem_pow_iff c
  constructor
  · intro hf
    rw [continuous_iff_continuousAt]
    intro g₀
    rw [ContinuousAt, Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε h1
    filter_upwards [(hf n).eventually_eq g₀] with g hg
    rw [dist_eq_norm, ← Subalgebra.coe_sub]
    exact lt_of_le_of_lt ((ha n _).1 (Ideal.Quotient.eq.1 hg)) hn
  · intro hf n
    rw [IsLocallyConstant.iff_eventually_eq]
    intro g₀
    filter_upwards [Metric.tendsto_nhds.1 (hf.tendsto g₀) (a ^ n) (pow_pos h0 n)] with g hg
    rw [dist_eq_norm, ← Subalgebra.coe_sub] at hg
    exact Ideal.Quotient.eq.2 ((ha n _).2 hg.le)
