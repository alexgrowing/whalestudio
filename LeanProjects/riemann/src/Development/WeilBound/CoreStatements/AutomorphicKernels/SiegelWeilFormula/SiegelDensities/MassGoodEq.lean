import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelDensities.Pieces

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.Densx

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.SW
open scoped TensorProduct ENNReal NNReal

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E}

open GlobalTheory.CompanionTheory.SW.GoodMass

theorem mass_good_eq (hE2 : PositivityTheory.PfSWUS.HMass.OneVecBinaryMass) (hO : MassOne) (hcm : IsCMExt F E σ) :
    ∀ (n : ℕ) (J : Matrix (Fin (n + 1)) (Fin (n + 1)) E), IsHermND σ J →
    ∀ (T : Matrix (Fin (n + 1)) (Fin (n + 1)) E) (hT : ∀ a b, σ (T b a) = T a b), T.det ≠ 0 →
    ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∃ C : ℝ,
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ lam, IsStdV v lam → ∀ m,
      IsGramFib (Fv F v) σ J (n + 1) (coordW (Fv F v) b lam (n + 1) (n + 1)) (coordHerm (Fv F v) σ b lam (n + 1)) m →
      |((cfac E v : ℝ≥0∞) * m (hermOf (Fv F v) σ T hT) (latV b v)).toReal - 1| ≤
        C / (Ideal.absNorm v.asIdeal : ℝ) ^ 2 := by
  intro n
  induction n with
  | zero =>
    intro J hJ T hT hdet d b
    obtain ⟨β, -, hβ0, hβ⟩ := GlobalTheory.T.hermitian_one_by_one_is_scalar F E σ hcm T hT
    have hβ0 := hβ0 hdet
    refine ⟨0, ?_⟩
    filter_upwards [hO F E σ hcm J hJ d b, (GlobalTheory.T.integral_almost_all_places F E σ hcm d b).2 β hβ0] with v hv hu lam hl m hm
    rw [hβ (Fv F v), hv lam hl m hm _ hu]
    simp
  | succ n ih =>
    intro J hJ T hT hdet d b
    obtain ⟨x, t, ht, hx⟩ := exists_aniso hcm T hT hdet
    obtain ⟨g, T₁, hT₁, hblock, -⟩ :=
      AlgSplit.split_anisotropic F E σ hcm (n + 1) T ⟨hT, hdet⟩ t x ht hx
    have hbh : ∀ a b, σ (blockOne (algebraMap F E t) T₁ b a) = blockOne (algebraMap F E t) T₁ a b :=
      blockOne_herm _ (σ.commutes t) _ hT₁.1
    have hgdet : (g : Matrix (Fin (n + 2)) (Fin (n + 2)) E).det ≠ 0 :=
      ((Matrix.isUnit_iff_isUnit_det _).1 g.isUnit).ne_zero
    have hone : IsHermND σ (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) E) := one_hermND (n + 1)
    have hJ' : IsHermND σ (blockOne (algebraMap F E t) (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) E)) :=
      blockOne_hermND t ht
    obtain ⟨C₁, hC₁⟩ := ih 1 hone T₁ hT₁.1 hT₁.2 d b
    obtain ⟨C₀, hC₀⟩ := PositivityTheory.PfSWUS.HMass.one_vec_bound hE2 hcm (n + 2) _ hJ' (by omega) b
    refine ⟨|C₀| + |C₁| + |C₀| * |C₁|, ?_⟩
    have e1 := GlobalTheory.T.local_densities_congruent_target_almost_all F E σ hcm (n + 2) J hJ (n + 2) T hT hdet g hgdet _ hbh hblock d b
    have e2 := GlobalTheory.T.local_gram_fiber_measures_agree_almost_all F E σ hcm (n + 2) J hJ _ hJ' d b (n + 2)
    have e3 := GlobalTheory.T.local_densities_block_one_almost_all F E σ hcm (n + 1) 1 hone t ht (n + 1) T₁ hT₁.1 hT₁.2 hbh d b
    have e5 := (GlobalTheory.T.integral_almost_all_places F E σ hcm d b).2 t ht
    filter_upwards [e1, e2, e3, hC₀, e5, hC₁] with v h1 h2 h3 h4 h5 h6 lam hl m hm
    obtain ⟨m', hm'⟩ := exists_family hcm hJ' b v lam hl (n + 2)
    obtain ⟨m₁, hm₁⟩ := exists_family hcm hJ' b v lam hl 1
    obtain ⟨m₂, hm₂⟩ := exists_family hcm hone b v lam hl (n + 1)
    have a1 := h1 lam hl m hm
    have a2 := h2 lam hl m m' hm hm' (hermOf (Fv F v) σ _ hbh)
    have a3 := h3 lam hl m' m₁ m₂ hm' hm₁ hm₂
    have a4 := h4 lam hl m₁ hm₁ _ h5
    have a6 := h6 lam hl m₂ hm₂
    rw [← a1, a2, a3, mul_left_comm, ENNReal.toReal_mul]
    exact PositivityTheory.PfSWUS.HMass.arith2 (absNorm_one_le v) a4 a6

end Main

theorem massCAll_of (hE2 : PositivityTheory.PfSWUS.HMass.OneVecBinaryMass) (hO : MassOne) : MassCAll := by
  intro F E _ _ _ _ _ σ hCM M hM J hJ T hT hdet d b lam hlam m hm
  obtain ⟨n, rfl⟩ : ∃ n, M = n + 1 := ⟨M - 1, by omega⟩
  refine ⟨?_, ?_⟩
  · intro v
    have hloc : IsLocR (Fv F v) := GlobalTheory.T.completion_is_local_ring F v
    obtain ⟨hTR, hLC, hSC, hT2, -⟩ := id hloc
    haveI := hTR
    haveI := hLC
    haveI := hSC
    haveI := hT2
    haveI : BorelSpace (Fv F v) := ⟨rfl⟩
    have hh := GlobalTheory.T.coordinate_haar_measure F E σ hCM (Fv F v) d b (lam v) (hlam v).1
    haveI hW := hh.2.1 (n + 1) (n + 1)
    haveI hH := hh.2.2 (n + 1)
    haveI hlf := (GlobalTheory.T.gram_fiber_measure_locallyFinite_and_ne_zero_of_isOpen F E σ hCM (n + 1) J hJ (Fv F v) hloc (n + 1) _ _ (m v) hW hH (hm v)
      (hermOf (Fv F v) σ T hT)).1
    rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.coe_lt_top (GlobalTheory.T.local_lattice_compact_open_unit_volume F E σ hCM d b (n + 1) (n + 1) v).1.measure_lt_top
  · obtain ⟨C, hC⟩ := mass_good_eq hE2 hO hCM n J hJ T hT hdet d b
    refine Summable.of_norm_bounded_eventually
      (g := fun v : HeightOneSpectrum (𝓞 F) => C * (1 / (Ideal.absNorm v.asIdeal : ℝ) ^ 2))
      ((GlobalTheory.CompanionTheory.SW.Primes.summable_one_div_absNorm_sq F).mul_left C) ?_
    filter_upwards [hC] with v hv
    have := hv (lam v) (hlam v) (m v) (hm v)
    rw [Real.norm_eq_abs, abs_abs, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
    simpa [div_eq_mul_inv] using this

end PositivityTheory.SiegelWeilFormula.Densx

end
