import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstMemberMaximalCompactPreservesPolynomialFock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchActionReadingsCompatible
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPairOfIsTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneLeftInverseExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneComplementSkewHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneComplementSignature
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneComplementLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneComplementDualLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneComplementCartan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneComplementSplitBasis
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaPairPolynomialCompactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilActionPreservesLintegralStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.KFixedVanish

open scoped Classical in

theorem exists_fixed {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (μ : Measure (κ → mixedEmbedding.mixedSpace F)) [μ.IsAddHaarMeasure]
    (U V : Submodule ℂ (SInf F κ)) (hV : FiniteDimensional ℂ V) (hUV : U ≤ V)
    (T : Set (SInf F κ →ₗ[ℂ] SInf F κ)) (hT : ∀ A ∈ T, ∀ v ∈ V, A v - v ∈ U)
    (hiso : ∀ A ∈ T, ∀ v : SInf F κ, ∫⁻ x, ‖A v x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖v x‖ₑ ^ 2 ∂μ) :
    ∀ f ∈ V, ∃ u ∈ U, ∀ A ∈ T, A (f - u) = f - u := by
  intro f hf
  have hB : BorelSpace (κ → mixedEmbedding.mixedSpace F) := inferInstance
  haveI hO : @OpensMeasurableSpace (κ → mixedEmbedding.mixedSpace F) (UniformSpace.toTopologicalSpace) _ := by
    convert @BorelSpace.opensMeasurable _ _ _ hB
  haveI hG : μ.HasTemperateGrowth :=
    @Measure.IsAddHaarMeasure.instHasTemperateGrowth _ _ _ _ inferInstance (by convert hB) μ _
  let J : SInf F κ →ₗ[ℂ] Lp ℂ 2 μ := (SchwartzMap.toLpCLM ℂ ℂ 2 μ).toLinearMap
  have hJ : ∀ g : SInf F κ, ((J g : Lp ℂ 2 μ) : (κ → mixedEmbedding.mixedSpace F) → ℂ) =ᵐ[μ] g :=
    fun g => SchwartzMap.coeFn_toLp g 2 μ
  have hnorm : ∀ g : SInf F κ, ‖J g‖ = ((∫⁻ x, ‖g x‖ₑ ^ 2 ∂μ) ^ (1 / 2 : ℝ)).toReal := by
    intro g
    rw [Lp.norm_def, eLpNorm_congr_ae (hJ g), eLpNorm_eq_lintegral_rpow_enorm (by norm_num) (by simp)]
    congr 2
    · simp only [ENNReal.toReal_ofNat]
      congr 1
      funext x
      exact ENNReal.rpow_two _
  have hinj : ∀ g : SInf F κ, J g = 0 → g = 0 := by
    intro g hg
    have h1 : (g : (κ → mixedEmbedding.mixedSpace F) → ℂ) =ᵐ[μ] (0 : (κ → mixedEmbedding.mixedSpace F) → ℂ) := by
      refine (hJ g).symm.trans ?_
      rw [hg]
      exact Lp.coeFn_zero _ _ _
    have h2 := (Continuous.ae_eq_iff_eq μ g.continuous continuous_const).1 h1
    ext x
    exact congrFun h2 x
  haveI : FiniteDimensional ℂ U := Submodule.finiteDimensional_of_le hUV
  set H : Submodule ℂ (Lp ℂ 2 μ) := U.map J with hH
  haveI : FiniteDimensional ℂ H := inferInstance
  obtain ⟨u, hu, hpu⟩ : ∃ u ∈ U, J u = H.starProjection (J f) := by
    have hm : H.starProjection (J f) ∈ H := by
      rw [Submodule.starProjection_apply]
      exact (H.orthogonalProjectionOnto (J f)).2
    obtain ⟨u, hu, e⟩ := Submodule.mem_map.1 hm
    exact ⟨u, hu, e⟩
  refine ⟨u, hu, fun A hA => ?_⟩
  have hw : f - u ∈ V := V.sub_mem hf (hUV hu)
  have horth : J (f - u) ∈ Hᗮ := by
    rw [map_sub, hpu]
    exact H.sub_starProjection_mem_orthogonal (J f)
  have h0 : inner ℂ (J (A (f - u) - (f - u))) (J (f - u)) = 0 :=
    Submodule.inner_right_of_mem_orthogonal (Submodule.mem_map_of_mem (hT A hA _ hw)) horth
  have hn : ‖J (A (f - u))‖ = ‖J (f - u)‖ := by rw [hnorm, hnorm, hiso A hA]
  rw [map_sub, inner_sub_left, sub_eq_zero] at h0
  have hsq : ‖J (A (f - u)) - J (f - u)‖ ^ 2 = 0 := by
    rw [@norm_sub_sq ℂ, h0, hn, inner_self_eq_norm_sq (𝕜 := ℂ)]
    ring
  have h3 : J (A (f - u) - (f - u)) = 0 := by
    rw [map_sub]
    exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 hsq)
  exact sub_eq_zero.1 (hinj _ h3)

end GlobalTheory.KFixedVanish

namespace GlobalTheory.KFixedVanish

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem kInf_mul {n : ℕ} {X : Spc F E n} {τ : ∀ w : InfinitePlace F, EmbOver E w} {k k' : UA σ X.J}
    (hk : k ∈ KInf σ X τ) (hk' : k' ∈ KInf σ X τ) : k * k' ∈ KInf σ X τ := by
  refine ⟨fun u hu => ?_, fun w => ?_⟩
  · have e : mat (k * k') - 1 = (mat k - 1) * mat k' + (mat k' - 1) := by
      change mat k * mat k' - 1 = _
      rw [Matrix.sub_mul, Matrix.one_mul]
      abel
    rw [e, smul_add, ← Matrix.smul_mul, hk.1 u hu, hk'.1 u hu, Matrix.zero_mul, add_zero]
  · change Commute ((mat k * mat k').map (piInf (τ w))) (X.θ w)
    rw [Matrix.map_mul]
    exact (hk.2 w).mul_left (hk'.2 w)

theorem kInf_one {n : ℕ} {X : Spc F E n} {τ : ∀ w : InfinitePlace F, EmbOver E w} : (1 : UA σ X.J) ∈ KInf σ X τ := by
  refine ⟨fun u _ => ?_, fun w => ?_⟩
  · change u • ((1 : Matrix (Fin n) (Fin n) (AE F E)) - 1) = 0
    rw [sub_self, smul_zero]
  · change Commute ((1 : Matrix (Fin n) (Fin n) (AE F E)).map (piInf (τ w))) (X.θ w)
    rw [Matrix.map_one _ (map_zero _) (map_one _)]
    exact Commute.one_left _

end GlobalTheory.KFixedVanish
