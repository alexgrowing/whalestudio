import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.MatNDHHolds

noncomputable section

namespace PI.AprimeInfW.GenericDensity

open scoped RealInnerProductSpace FourierTransform
open MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {V W ι : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [MeasurableSpace V]
  [BorelSpace V] [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W] [MeasurableSpace W]
  [BorelSpace W] [Fintype ι] [DecidableEq ι]

private theorem exists_linearMap_inner_eq_and_det_eq_gram_det (β : W → W → ℝ)
    (hL : ∀ x x' y, β (x + x') y = β x y + β x' y) (hR : ∀ x y y', β x (y + y') = β x y + β x y')
    (hcL : ∀ y, Continuous fun x => β x y) (hcR : ∀ x, Continuous fun y => β x y)
    (b : OrthonormalBasis ι ℝ W) :
    ∃ A : W →ₗ[ℝ] W, (∀ x y, β x y = ⟪x, A y⟫) ∧
      LinearMap.det A = (Matrix.of fun i j => β (b i) (b j)).det := by
  have sL : ∀ (r : ℝ) x y, β (r • x) y = r * β x y := fun r x y =>
    map_real_smul (AddMonoidHom.mk' (fun x => β x y) (fun x x' => hL x x' y)) (hcL y) r x
  have sR : ∀ (r : ℝ) x y, β x (r • y) = r * β x y := fun r x y =>
    map_real_smul (AddMonoidHom.mk' (fun y => β x y) (fun y y' => hR x y y')) (hcR x) r y
  let A : W →ₗ[ℝ] W :=
    { toFun := fun y => ∑ i, β (b i) y • b i
      map_add' := fun y y' => by simp only [hR, add_smul, Finset.sum_add_distrib]
      map_smul' := fun r y => by simp only [sR, mul_smul, Finset.smul_sum, RingHom.id_apply] }
  have hA : ∀ x y, β x y = ⟪x, A y⟫ := by
    intro x y
    have h1 : β x y = ∑ i, ⟪b i, x⟫ * β (b i) y := by
      conv_lhs => rw [← b.sum_repr' x]
      change (AddMonoidHom.mk' (fun x => β x y) (fun x x' => hL x x' y)) (∑ i, ⟪b i, x⟫ • b i) = _
      rw [map_sum]
      simp [sL]
    have h2 : ⟪x, A y⟫ = ∑ i, β (b i) y * ⟪x, b i⟫ := by
      simp [A, inner_sum, inner_smul_right]
    rw [h1, h2]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [real_inner_comm, mul_comm]
  refine ⟨A, hA, ?_⟩
  rw [← LinearMap.det_toMatrix b.toBasis]
  congr 1
  ext i j
  rw [LinearMap.toMatrix_apply, Matrix.of_apply, hA]
  simp [OrthonormalBasis.repr_apply_apply]

private theorem integral_fourier_map_eq_neg_of_integrable (μ : Measure V) (χ : V → V → ℂ) (hμ : SelfDual μ χ) (e : V ≃ₜ W)
    (he : ∀ x y, e (x + y) = e x + e y) (β : W → W → ℝ)
    (hχ : ∀ x y, χ (e.symm x) (e.symm y) = ((𝐞 (β x y) : Circle) : ℂ))
    (Φ : W → ℂ) (hΦc : Continuous Φ) (hΦs : HasCompactSupport Φ)
    (hint : Integrable (fun y => ∫ x, Φ x * ((𝐞 (β x y) : Circle) : ℂ) ∂(μ.map e)) (μ.map e))
    (z : W) :
    ∫ y, (∫ x, Φ x * ((𝐞 (β x y) : Circle) : ℂ) ∂(μ.map e)) * ((𝐞 (β y z) : Circle) : ℂ) ∂(μ.map e)
      = Φ (-z) := by
  have hme : MeasurableEmbedding e := e.measurableEmbedding
  have hmap : ∀ g : W → ℂ, ∫ w, g w ∂(μ.map e) = ∫ x, g (e x) ∂μ := fun g => hme.integral_map g
  have hχ' : ∀ x y, χ x y = ((𝐞 (β (e x) (e y)) : Circle) : ℂ) := fun x y => by
    simpa using hχ (e x) (e y)
  set F := fun y => ∫ x, Φ x * ((𝐞 (β x y) : Circle) : ℂ) ∂(μ.map e) with hFdef
  have hF : ∀ y, ∫ x, (Φ ∘ e) x * χ x y ∂μ = F (e y) := by
    intro y
    simp only [hFdef, hmap, Function.comp_apply, hχ']
  have hint' : Integrable (fun y => ∫ x, (Φ ∘ e) x * χ x y ∂μ) μ := by
    simp only [hF]
    exact hme.integrable_map_iff.mp hint
  have key := hμ.2 (Φ ∘ e) (hΦc.comp e.continuous) (hΦs.comp_homeomorph e) hint' (e.symm z)
  have hneg : e (-(e.symm z)) = -z := by
    have := map_neg (AddMonoidHom.mk' e he) (e.symm z)
    simpa using this
  simp only [hF, hχ', Homeomorph.apply_symm_apply, Function.comp_apply, hneg] at key
  rw [hmap]
  simp only [hFdef, hmap]
  exact key

private theorem false_of_degenerate_of_fourier_inversion (ν : Measure W) [ν.IsAddHaarMeasure] (β : W → W → ℝ)
    (hL : ∀ x x' y, β (x + x') y = β x y + β x' y) (hcL : ∀ y, Continuous fun x => β x y)
    (k : W) (hk : k ≠ 0) (hk0 : ∀ y, β k y = 0)
    (hP : ∀ Φ : W → ℂ, Continuous Φ → HasCompactSupport Φ →
      Integrable (fun y => ∫ x, Φ x * ((𝐞 (β x y) : Circle) : ℂ) ∂ν) ν → ∀ z : W,
      ∫ y, (∫ x, Φ x * ((𝐞 (β x y) : Circle) : ℂ) ∂ν) * ((𝐞 (β y z) : Circle) : ℂ) ∂ν = Φ (-z)) :
    False := by
  have hkpos : 0 < ‖k‖ := norm_pos_iff.mpr hk
  let bump : ContDiffBump (0 : W) := ⟨‖k‖ / 2, ‖k‖, by positivity, by linarith⟩
  let ψ : W → ℂ := fun x => ((bump x : ℝ) : ℂ)
  have hψc : Continuous ψ := Complex.continuous_ofReal.comp bump.continuous
  have hψs : HasCompactSupport ψ := bump.hasCompactSupport.comp_left Complex.ofReal_zero
  have hψs' : HasCompactSupport (fun x => ψ (x + k)) := hψs.comp_homeomorph (Homeomorph.addRight k)
  let Φ : W → ℂ := fun x => ψ x - ψ (x + k)
  have hΦc : Continuous Φ := hψc.sub (hψc.comp (continuous_add_right k))
  have hΦs : HasCompactSupport Φ := hψs.sub hψs'
  have hzero : ∀ y, ∫ x, Φ x * ((𝐞 (β x y) : Circle) : ℂ) ∂ν = 0 := by
    intro y
    let g : W → ℂ := fun x => ψ x * ((𝐞 (β x y) : Circle) : ℂ)
    have hgc : Continuous g := by
      have := hcL y
      fun_prop
    have hg : Integrable g ν := hgc.integrable_of_hasCompactSupport hψs.mul_right
    have heq : (fun x => Φ x * ((𝐞 (β x y) : Circle) : ℂ)) = fun x => g x - g (x + k) := by
      funext x
      simp only [Φ, g, hL, hk0, add_zero]
      ring
    rw [heq, integral_sub hg (hg.comp_add_right k), integral_add_right_eq_self, sub_self]
  have hint : Integrable (fun y => ∫ x, Φ x * ((𝐞 (β x y) : Circle) : ℂ) ∂ν) ν := by
    simp only [hzero]
    exact integrable_zero _ _ _
  have key := hP Φ hΦc hΦs hint 0
  simp only [hzero, zero_mul, integral_zero, neg_zero] at key
  have h0 : bump 0 = 1 := bump.one_of_mem_closedBall (by simp; positivity)
  have h1 : bump k = 0 := by
    apply Function.notMem_support.mp
    rw [bump.support_eq]
    simp
    exact le_rfl
  simp [Φ, ψ, h0, h1] at key

private theorem measure_eq_sqrt_abs_det_smul_volume_of_inversion (ν : Measure W) [ν.IsAddHaarMeasure] (A : W →ₗ[ℝ] W)
    (hdet : LinearMap.det A ≠ 0)
    (hP : ∀ Φ : W → ℂ, Continuous Φ → HasCompactSupport Φ →
      Integrable (fun y => ∫ x, Φ x * ((𝐞 ⟪x, A y⟫ : Circle) : ℂ) ∂ν) ν → ∀ z : W,
      ∫ y, (∫ x, Φ x * ((𝐞 ⟪x, A y⟫ : Circle) : ℂ) ∂ν) * ((𝐞 ⟪A y, z⟫ : Circle) : ℂ) ∂ν = Φ (-z)) :
    ν = ENNReal.ofReal (Real.sqrt |LinearMap.det A|) • volume := by
  set s := ν.addHaarScalarFactor volume with hsdef
  have hs : 0 < s := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure ν volume
  have hν : ν = (s : ENNReal) • volume := by
    rw [← ENNReal.smul_def]
    exact Measure.isAddLeftInvariant_eq_smul ν volume
  let bump : ContDiffBump (0 : W) := ⟨1, 2, one_pos, one_lt_two⟩
  have h0 : bump 0 = 1 := bump.one_of_mem_closedBall (by simp; exact bump.rIn_pos.le)
  let Φ : W → ℂ := fun x => ((bump x : ℝ) : ℂ)
  have hΦs : HasCompactSupport Φ := bump.hasCompactSupport.comp_left Complex.ofReal_zero
  have hΦd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ :=
    Complex.ofRealCLM.contDiff.comp (bump.contDiff (n := ⊤))
  let S : SchwartzMap W ℂ := hΦs.toSchwartzMap hΦd
  have hSΦ : (S : W → ℂ) = Φ := rfl
  let g : W → ℂ := 𝓕⁻ Φ
  have hgS : g = ⇑(𝓕⁻ S : SchwartzMap W ℂ) := by rw [SchwartzMap.fourierInv_coe, hSΦ]
  have hgi : Integrable g := by rw [hgS]; exact (𝓕⁻ S : SchwartzMap W ℂ).integrable
  have hgg : ∫ v, g v = 1 := by
    have h1 : 𝓕⁻ g 0 = ∫ v, g v := by simp [Real.fourierInv_eq]
    have h2 : 𝓕⁻ g 0 = Φ 0 := by
      rw [Real.fourierInv_eq_fourier_neg, hgS, ← SchwartzMap.fourier_coe,
        FourierInvPair.fourier_fourierInv_eq, hSΦ, neg_zero]
    rw [← h1, h2]
    simp [Φ, h0]
  have hAc : Continuous A := A.continuous_of_finiteDimensional
  have hAm : AEMeasurable A volume := hAc.measurable.aemeasurable
  have hmapA : (volume : Measure W).map A = ENNReal.ofReal |(LinearMap.det A)⁻¹| • volume :=
    Measure.map_linearMap_addHaar_eq_smul_addHaar volume hdet
  have hgim : Integrable g ((volume : Measure W).map A) := by
    rw [hmapA]
    exact hgi.smul_measure ENNReal.ofReal_ne_top
  have hgA : Integrable (fun y => g (A y)) volume :=
    (integrable_map_measure hgim.aestronglyMeasurable hAm).mp hgim
  have hinner : ∀ y, ∫ x, Φ x * ((𝐞 ⟪x, A y⟫ : Circle) : ℂ) ∂ν = (s : ℝ) • g (A y) := by
    intro y
    show _ = (s : ℝ) • 𝓕⁻ Φ (A y)
    rw [hν, integral_smul_measure, ENNReal.coe_toReal, Real.fourierInv_eq]
    congr 1
    congr 1
    funext x
    rw [Circle.smul_def, smul_eq_mul, mul_comm]
  have hint : Integrable (fun y => ∫ x, Φ x * ((𝐞 ⟪x, A y⟫ : Circle) : ℂ) ∂ν) ν := by
    simp only [hinner]
    rw [hν]
    exact (hgA.smul (s : ℝ)).smul_measure ENNReal.coe_ne_top
  have hcomp : ∫ y, g (A y) = (ENNReal.ofReal |(LinearMap.det A)⁻¹|).toReal • (1 : ℂ) := by
    rw [← integral_map hAm hgim.aestronglyMeasurable, hmapA, integral_smul_measure, hgg]
  have key := hP Φ hΦd.continuous hΦs hint 0
  simp only [hinner, inner_zero_right, AddChar.map_zero_eq_one, Circle.coe_one, mul_one] at key
  rw [hν, integral_smul_measure, integral_smul, hcomp, ENNReal.coe_toReal,
    ENNReal.toReal_ofReal (abs_nonneg _)] at key
  have hreal : (s : ℝ) * ((s : ℝ) * |(LinearMap.det A)⁻¹|) = 1 := by
    have h2 : Φ (-0) = 1 := by simp [Φ, h0]
    rw [h2] at key
    have := congrArg Complex.re key
    simp only [Complex.smul_re, Complex.one_re, smul_eq_mul, mul_one] at this
    exact this
  have hdpos : 0 < |LinearMap.det A| := abs_pos.mpr hdet
  have hsq : (s : ℝ) ^ 2 = |LinearMap.det A| := by
    rw [abs_inv] at hreal
    field_simp at hreal
    nlinarith [hreal]
  rw [hν]
  congr 1
  rw [← ENNReal.ofReal_coe_nnreal, ← hsq, Real.sqrt_sq s.coe_nonneg]

theorem dens_generic (μ : Measure V) (χ : V → V → ℂ) (hμ : SelfDual μ χ) (e : V ≃ₜ W)
    (he : ∀ x y, e (x + y) = e x + e y) (β : W → W → ℝ)
    (hχ : ∀ x y, χ (e.symm x) (e.symm y) = ((𝐞 (β x y) : Circle) : ℂ))
    (hL : ∀ x x' y, β (x + x') y = β x y + β x' y) (hR : ∀ x y y', β x (y + y') = β x y + β x y')
    (hcL : ∀ y, Continuous fun x => β x y) (hcR : ∀ x, Continuous fun y => β x y)
    (hS : ∀ x y, β x y = β y x) (b : OrthonormalBasis ι ℝ W) :
    μ.map e = ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j => β (b i) (b j)).det|) • volume := by
  obtain ⟨A, hA, hdet⟩ := exists_linearMap_inner_eq_and_det_eq_gram_det β hL hR hcL hcR b
  have hP := fun Φ hc hs hi z => integral_fourier_map_eq_neg_of_integrable μ χ hμ e he β hχ Φ hc hs hi z
  haveI : μ.IsAddHaarMeasure := hμ.1
  haveI : (μ.map e).IsAddHaarMeasure :=
    Measure.isAddHaarMeasure_map μ (AddMonoidHom.mk' e he) e.continuous e.surjective
      e.isClosedEmbedding.tendsto_cocompact
  by_cases hd : (Matrix.of fun i j => β (b i) (b j)).det = 0
  · exfalso
    rw [← hdet] at hd
    obtain ⟨k, hkker, hk⟩ :=
      Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.det_eq_zero_iff_ker_ne_bot.mp hd)
    have hk0 : ∀ y, β k y = 0 := fun y => by
      rw [hS, hA, LinearMap.mem_ker.mp hkker, inner_zero_right]
    exact false_of_degenerate_of_fourier_inversion (μ.map e) β hL hcL k hk hk0 hP
  · rw [← hdet] at hd ⊢
    apply measure_eq_sqrt_abs_det_smul_volume_of_inversion (μ.map e) A hd
    intro Φ hc hs hi z
    have hβ' : ∀ y z, ⟪A y, z⟫ = β y z := fun y z => by rw [hS, hA, real_inner_comm]
    simp only [← hA, hβ'] at hi ⊢
    exact hP Φ hc hs hi z

end PI.AprimeInfW.GenericDensity
