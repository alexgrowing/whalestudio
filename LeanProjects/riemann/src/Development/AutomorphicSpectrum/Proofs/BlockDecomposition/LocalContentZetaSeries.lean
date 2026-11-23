import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsContent
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorIntegerRingAlmostAllPlaces
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalRankOneDensityUniformizerPower
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSquareMulOfNonsquareUnits
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalUnitScalingNormMeasureStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuadraticBasisIntegralUnramifiedStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuadraticBasisIntegralOrderStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypMass

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypMass.Content

theorem one_lt_qv {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) : 1 < (qv v : ℝ) := by
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := fun h => v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have : 1 < Ideal.absNorm v.asIdeal := by omega
  simp only [qv, NNReal.coe_natCast]
  exact_mod_cast this

theorem hasSum_field (q : ℝ) (hq : 1 < q) (s : ℕ) (hs : 1 ≤ s) :
    HasSum (fun k : ℕ => ((q ^ (2 * k))⁻¹) ^ s) (1 - (q ^ (2 * s))⁻¹)⁻¹ := by
  have h0 : 0 < q := by linarith
  have hr : (q ^ (2 * s))⁻¹ < 1 := inv_lt_one_of_one_lt₀ (one_lt_pow₀ hq (by omega))
  have := hasSum_geometric_of_lt_one (r := (q ^ (2 * s))⁻¹) (by positivity) hr
  convert this using 2 with k
  rw [inv_pow, inv_pow, ← pow_mul, ← pow_mul]
  congr 2
  ring

theorem hasSum_split (q : ℝ) (hq : 1 < q) (s : ℕ) (hs : 1 ≤ s) :
    HasSum (fun p : ℕ × ℕ => ((q ^ (p.1 + p.2))⁻¹) ^ s) (((1 - (q ^ s)⁻¹)⁻¹) ^ 2) := by
  have h0 : 0 < q := by linarith
  have hr : (q ^ s)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (one_lt_pow₀ hq (by omega))
  have hg := hasSum_geometric_of_lt_one (r := (q ^ s)⁻¹) (by positivity) hr
  have hn : Summable fun k : ℕ => ‖((q ^ s)⁻¹) ^ k‖ := hg.summable.norm
  have := hg.mul hg (summable_mul_of_summable_norm hn hn)
  have e : (fun p : ℕ × ℕ => ((q ^ (p.1 + p.2))⁻¹) ^ s) = fun p : ℕ × ℕ => ((q ^ s)⁻¹) ^ p.1 * ((q ^ s)⁻¹) ^ p.2 := by
    funext p
    rw [← pow_add, inv_pow, inv_pow, ← pow_mul, ← pow_mul, mul_comm s]
  rw [e, pow_two]
  exact this

theorem content : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∃ (ι : Type) (_ : Countable ι) (c : ι → Fv F v ⊗[F] E) (w : ι → ℕ), IsContent σ b v c w ∧ ∀ s : ℕ, 1 ≤ s → HasSum (fun i => (((qv v : ℝ) ^ w i)⁻¹) ^ s) (zetaV E v s) := by
  intro F E _ _ _ _ _ σ h d b
  have hinv : ∀ x, σ (σ x) = x := fun x => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [h.2.2.2, h.2.2.2, star_star]
  have hne : ∃ x, σ x ≠ x := by
    by_contra hc
    push_neg at hc
    obtain ⟨w⟩ := (inferInstance : Nonempty (NumberField.InfinitePlace E))
    have hreal : w.IsReal := by
      rw [← NumberField.InfinitePlace.mk_embedding w, NumberField.InfinitePlace.isReal_mk_iff,
        NumberField.ComplexEmbedding.isReal_iff]
      refine RingHom.ext fun x ↦ ?_
      rw [NumberField.ComplexEmbedding.conjugate_coe_eq]
      change star (w.embedding x) = w.embedding x
      rw [← h.2.2.2, hc]
    exact NumberField.InfinitePlace.not_isReal_iff_isComplex.2 (h.2.1.isComplex w) hreal
  obtain ⟨D, b₂, hsq, hb0, hσ1, hD⟩ := GlobalTheory.QuadNormBase.exists_basis F E σ h.2.2.1 hinv hne
  have hD0 : D ≠ 0 := fun h0 => hsq (h0 ▸ IsSquare.zero)
  have I := GlobalTheory.T.integral_almost_all_places F E σ h
  filter_upwards [(I d b).2 D hD0, (I d b).2 2 two_ne_zero,
    Filter.eventually_all.2 fun k => (I 2 b₂).1 (b k),
    Filter.eventually_all.2 fun j => (I d b).1 (b₂ j)] with v hD1 h21 hBC hCB
  have hq := one_lt_qv v
  by_cases hres : ∃ e : v.adicCompletionIntegers F, Valued.v ((e : Fv F v) ^ 2 - algebraMap F (Fv F v) D) < 1
  · obtain ⟨e, he⟩ : ∃ e : Fv F v, e ^ 2 = algebraMap F (Fv F v) D := by
      obtain ⟨e, he⟩ := hres
      have hDR : algebraMap F (Fv F v) D ∈ v.adicCompletionIntegers F := hD1.le
      have h2' : Valued.v (2 : Fv F v) = 1 := by simpa [map_ofNat] using h21
      have := GlobalTheory.QNorm.isSquare_of_isSquare_residue_odd F v h2' ⟨_, hDR⟩ hD1 ?_
      · obtain ⟨r, hr⟩ := this
        exact ⟨r, by rw [pow_two]; exact hr.symm⟩
      · refine ⟨IsLocalRing.residue _ e, ?_⟩
        rw [← map_mul, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal,
          mem_nonunits_iff, HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
        intro h1
        have : Valued.v ((e : Fv F v) ^ 2 - algebraMap F (Fv F v) D) = 1 := by
          rw [← Valuation.map_neg]
          simpa [pow_two] using h1
        exact absurd he (by rw [this]; exact lt_irrefl _)
    obtain ⟨hnf, c, c1, c3, c4, c5⟩ := GlobalTheory.T.quadratic_basis_integral_order F E σ h d b b₂ D hb0 hσ1 hD v hD1 h21 hBC hCB e he
    refine ⟨ℕ × ℕ, inferInstance, c, fun i => i.1 + i.2, ⟨c1, ?_, c3, c4, c5⟩, ?_⟩
    · intro i lam hlam
      obtain ⟨t, ht, hn⟩ := c3 i
      exact GlobalTheory.T.local_unit_scaling_norm_measure F E σ h d b v lam hlam (c i) t _ (c1 i).1 ht hn
    · intro s hs
      rw [zetaV, if_neg hnf]
      exact hasSum_split _ hq s hs
  · obtain ⟨hf, c, c1, c3, c4, c5⟩ := GlobalTheory.T.quadratic_basis_integral_unramified F E σ h d b b₂ D hb0 hσ1 hD v hD1 h21 hBC hCB hres
    refine ⟨ℕ, inferInstance, c, fun i => 2 * i, ⟨c1, ?_, c3, c4, c5⟩, ?_⟩
    · intro i lam hlam
      obtain ⟨t, ht, hn⟩ := c3 i
      exact GlobalTheory.T.local_unit_scaling_norm_measure F E σ h d b v lam hlam (c i) t _ (c1 i).1 ht hn
    · intro s hs
      rw [zetaV, if_pos hf]
      exact hasSum_field _ hq s hs

end GlobalTheory.CompanionTheory.WeilSiegel.HypMass.Content
