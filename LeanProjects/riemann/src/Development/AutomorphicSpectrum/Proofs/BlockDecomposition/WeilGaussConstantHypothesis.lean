import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WSteps
import GroundTheory.LocalFields.QuadraticAbelian.WeilRepQuadratic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GTil
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilModulusHypothesis
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsHaarMeasureComapSubtype
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuadraticExtensionTestVectorBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSchwartzZetaSeparatingCharacterStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuadraticCharacterNormGroupStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilConstantQuadraticCharacterStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormGroupIndexTwoStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzNormFormPullbackStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousAlgebraNormStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilGaussConstantSquareStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilGaussConstantNormOneStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousEqOfSchwartzPairingStatement
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel NNReal ENNReal

noncomputable section
namespace GlobalTheory.CompanionTheory.GaussLam

theorem ptw : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E] [Algebra.IsSeparable F E] [Fact (Module.finrank F E = 2)] (χ : AddChar F Circle), Continuous χ → χ ≠ 1 → ∀ σ : E ≃ₐ[F] E, σ ≠ AlgEquiv.refl → ∀ η : Fˣ →* ℂˣ, Continuous η → (∀ a : Fˣ, ((η a : ℂˣ) : ℂ) = nsg E (a : F)) → ∀ γ : ℂ, (∀ (a : Fˣ), ∀ Φ ∈ SBE E, ∫ u, (χ ((a : F) * Algebra.norm F u) : ℂ) * FTE E χ σ Φ u ∂muE E χ = γ * nsg E (a : F) * (((modulus (a : F) : ℝ)⁻¹ : ℝ) : ℂ) * ∫ z, (χ (-(Algebra.norm F z) / a) : ℂ) * Φ z ∂muE E χ) → ∀ g : F → ℂ, g ∈ schwartzBruhat F → g 0 = 0 → ∀ w : E, localFourier (muE E χ) (chE E χ) (fun x : E => localFourier (selfDualMeasure χ) χ g (Algebra.norm F x)) w = γ * GlobalTheory.CompanionTheory.GaussLam.hAvg E χ g (Algebra.norm F w) := by
  intro F _ _ _ _ _ _ E _ _ _ _ _ _ _ _ _ _ _ χ hχ hχ1 σ hσ η hcη hη γ hγ g hg g0 w
  have hcE : Continuous (chE E χ) := GroundTheory.LocalField.continuous_traceChar hχ hχ1
  have hnE : chE E χ ≠ 1 := GroundTheory.LocalField.traceChar_ne_one hχ hχ1
  have hf := localFourier_mem_schwartzBruhat (selfDualMeasure χ) hχ hχ1 hg
  have hΨ := GlobalTheory.T.schwartz_norm_form_pullback F E _ hf
  have hFΨ := localFourier_mem_schwartzBruhat (muE E χ) hcE hnE hΨ
  have hσ1 : σ = GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.conj F E := by
    rcases GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.eq_one_or_eq_conj σ with h | h
    · exact absurd h hσ
    · exact h
  have hσc : Continuous σ.symm := by
    have : (σ.symm : E → E) = GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.conj F E := by
      funext x
      apply σ.injective
      rw [AlgEquiv.apply_symm_apply, hσ1, GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.conj_conj]
    rw [this]
    exact GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.continuous_conj
  have hgt := (GlobalTheory.T.quadratic_character_norm_group F E η hcη hη g hg g0).1
  have hh : Continuous (GlobalTheory.CompanionTheory.GaussLam.hAvg E χ g) := by
    have e : GlobalTheory.CompanionTheory.GaussLam.hAvg E χ g = localFourier (selfDualMeasure χ) χ (GlobalTheory.CompanionTheory.GaussLam.gTil E g) :=
      funext fun t => (GlobalTheory.T.weil_constant_quadratic_character F E χ hχ η hcη hη g hg g0 t).symm
    rw [e]
    exact (localFourier_mem_schwartzBruhat (selfDualMeasure χ) hχ hχ1 hgt).1.continuous
  have hP := hFΨ.1.continuous.comp hσc
  have hQ : Continuous fun z : E => γ * GlobalTheory.CompanionTheory.GaussLam.hAvg E χ g (Algebra.norm F z) :=
    continuous_const.mul (hh.comp (GlobalTheory.T.continuous_algebra_norm F E))
  have key := GlobalTheory.T.continuous_eq_of_schwartz_pairing E (muE E χ) _ _ hP hQ (fun Φ hΦ => by
    simp only [Function.comp_apply]
    rw [← GlobalTheory.T.weil_gauss_constant_square F E χ hχ hχ1 σ Φ hΦ g hg]
    have e2 : ∫ z, Φ z * (γ * GlobalTheory.CompanionTheory.GaussLam.hAvg E χ g (Algebra.norm F z)) ∂muE E χ =
        γ * ∫ z, Φ z * GlobalTheory.CompanionTheory.GaussLam.hAvg E χ g (Algebra.norm F z) ∂muE E χ := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      simp only
      ring
    rw [e2, ← GlobalTheory.T.weil_gauss_constant_norm_one F E χ hχ hχ1 η hcη hη Φ hΦ g hg g0, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
    simp only
    by_cases ha : a = 0
    · subst ha
      simp [g0]
    · have := hγ (Units.mk0 a ha) Φ hΦ
      simp only [Units.val_mk0] at this
      rw [this]
      ring)
  have h1 := congrFun key (σ w)
  simp only [Function.comp_apply, AlgEquiv.symm_apply_apply] at h1
  rw [h1, Algebra.norm_eq_of_algEquiv]

theorem zeta_fe {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [MeasurableSpace K] [BorelSpace K] {ψ : AddChar K Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
    {μ : Kˣ →* ℂˣ} (hμ : IsUnit1 μ) {f : K → ℂ} (hf : f ∈ schwartzBruhat K) :
    localZeta (localFourier (selfDualMeasure ψ) ψ f) μ⁻¹ (1 / 2) = gam ψ μ (1 / 2) * localZeta f μ (1 / 2) := by
  have he : quasiCharExponent μ = 0 := by simp [quasiCharExponent, hμ.2]
  have hs1 : -quasiCharExponent μ < ((1 / 2 : ℂ)).re := by rw [he]; norm_num
  have hs2 : ((1 / 2 : ℂ)).re < 1 - quasiCharExponent μ := by rw [he]; norm_num
  have hs' : -quasiCharExponent μ⁻¹ < ((1 : ℂ) - 1 / 2).re := by
    rw [quasiCharExponent_inv, Complex.sub_re, Complex.one_re]
    linarith
  have hL1 := localLFactor_ne_zero hμ.1 hs1
  have hL2 := localLFactor_ne_zero (continuous_quasiChar_inv hμ.1) hs'
  have hfe := localZeta_functionalEquation hψ hψ1 hμ.1 hf hs1 hs2
  have h12 : (1 : ℂ) - 1 / 2 = 1 / 2 := by norm_num
  unfold gam
  rw [h12] at hfe hL2 ⊢
  field_simp at hfe ⊢
  linear_combination hfe

theorem isUnit1_one {K : Type} [Field K] [TopologicalSpace K] : IsUnit1 (1 : Kˣ →* ℂˣ) :=
  ⟨continuous_const, fun x => by simp⟩

theorem wGaussLam : Ad3.K.GL2LocalData.WGaussLam := by
  intro F _ _ _ _ _ _ _ χ hχ hχ1 E _ _ _ _ _ _ _ hd hc σ hσ η hη γ hγ
  haveI : ValuativeExtension F E := GlobalTheory.CompanionTheory.NormModulus.valuativeExtension_of_continuous hc
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ hd
  haveI : Fact (Module.finrank F E = 2) := ⟨hd⟩
  haveI : Algebra.IsSeparable F E := inferInstance
  have hex : ∀ a : Fˣ, (∃ t : Eˣ, Algebra.norm F (t : E) = (a : F)) ↔
      a ∈ (normUnits F E).range := by
    refine fun a => ⟨fun ⟨t, ht⟩ => ⟨t, Units.ext ((coe_normUnits t).trans ht)⟩, ?_⟩
    rintro ⟨t, rfl⟩
    exact ⟨t, (coe_normUnits t).symm⟩
  have hq : η = GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.quadChar F E := by
    ext a
    rw [hη a]
    unfold Ad3.K.GL2LocalData.nsg
    by_cases ha : a ∈ (normUnits F E).range
    · rw [if_pos ((hex a).2 ha), GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.quadChar_apply_of_mem ha, Units.val_one]
    · rw [if_neg (fun h => ha ((hex a).1 h)), GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.quadChar_apply_of_notMem ha]
      simp
  have hcη : Continuous η := by
    refine continuous_of_continuousAt_one η ?_
    have hker : IsOpen (η.ker : Set Fˣ) := by
      rw [hq]
      exact GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.isOpen_ker_quadChar
    have hev : (fun _ : Fˣ => (1 : ℂˣ)) =ᶠ[nhds 1] η := by
      filter_upwards [hker.mem_nhds (one_mem η.ker)] with x hx
      exact (MonoidHom.mem_ker.1 hx).symm
    have h0 : ContinuousAt (fun _ : Fˣ => (1 : ℂˣ)) 1 := continuousAt_const
    exact h0.congr hev
  have hu : IsUnit1 η := ⟨hcη, fun a => by
    rw [hη]
    unfold Ad3.K.GL2LocalData.nsg
    split_ifs <;> simp⟩
  obtain ⟨t, ht⟩ : ∃ t : Fˣ, η t = -1 := by
    by_contra hno
    apply GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.quadChar_ne_one (K := F) (E := E)
    ext a
    by_cases ha : a ∈ (normUnits F E).range
    · rw [GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.quadChar_apply_of_mem ha]; simp
    · exact absurd ⟨a, by rw [hq, GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.quadChar_apply_of_notMem ha]⟩ hno
  have hcE : Continuous (chE E χ) := GroundTheory.LocalField.continuous_traceChar hχ hχ1
  have hnE : chE E χ ≠ 1 := GroundTheory.LocalField.traceChar_ne_one hχ hχ1
  obtain ⟨κ, hκ, hfib⟩ := GlobalTheory.CompanionTheory.NormFib.wFib F χ hχ hχ1 E hd hc σ hσ η hη
  obtain ⟨g, hg, g0, hA, hB⟩ := GlobalTheory.T.exists_schwartz_zeta_separating_character F η hcη t ht
  obtain ⟨hgt, hZ⟩ := GlobalTheory.T.quadratic_character_norm_group F E η hcη hη g hg g0
  have hf := localFourier_mem_schwartzBruhat (selfDualMeasure χ) hχ hχ1 hg
  have hft := localFourier_mem_schwartzBruhat (selfDualMeasure χ) hχ hχ1 hgt

  have hpt := ptw F E χ hχ hχ1 σ hσ η hcη hη γ hγ g hg g0
  have hΨ := GlobalTheory.T.schwartz_norm_form_pullback F E _ hf

  have hE := zeta_fe hcE hnE (isUnit1_one (K := E)) hΨ
  rw [inv_one, GlobalTheory.CompanionTheory.LanglandsConstant.gam_one_half, one_mul] at hE
  have hfun : localFourier (selfDualMeasure (chE E χ)) (chE E χ)
      (fun x : E => localFourier (selfDualMeasure χ) χ g (Algebra.norm F x)) =
      fun w => γ * localFourier (selfDualMeasure χ) χ (GlobalTheory.CompanionTheory.GaussLam.gTil E g) (Algebra.norm F w) := by
    funext w
    rw [GlobalTheory.T.weil_constant_quadratic_character F E χ hχ η hcη hη g hg g0]
    exact hpt w
  rw [hfun] at hE
  have hscal : localZeta (fun w : E => γ * localFourier (selfDualMeasure χ) χ (GlobalTheory.CompanionTheory.GaussLam.gTil E g) (Algebra.norm F w)) 1 (1 / 2) =
      γ * localZeta (fun w : E => localFourier (selfDualMeasure χ) χ (GlobalTheory.CompanionTheory.GaussLam.gTil E g) (Algebra.norm F w)) 1 (1 / 2) := by
    unfold localZeta
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [mul_assoc]
  rw [hscal, GlobalTheory.T.norm_group_index_two F E η hcη hη κ hfib _ hf, GlobalTheory.T.norm_group_index_two F E η hcη hη κ hfib _ hft] at hE
  have e1 := zeta_fe hχ hχ1 (isUnit1_one (K := F)) hg
  have e2 := zeta_fe hχ hχ1 hu hg
  have e3 := zeta_fe hχ hχ1 (isUnit1_one (K := F)) hgt
  have e4 := zeta_fe hχ hχ1 hu hgt
  have hinv : η⁻¹ = η := by
    ext a
    have h2 := GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.quadChar_sq (K := F) (E := E) a
    rw [← hq] at h2
    have : (η a)⁻¹ = η a := by
      rw [inv_eq_iff_mul_eq_one, ← sq, h2]
    simp [this]
  rw [inv_one, GlobalTheory.CompanionTheory.LanglandsConstant.gam_one_half, one_mul] at e1 e3
  rw [hinv] at e2 e4
  have z1 := hZ 1
  have z2 := hZ η
  simp only [inv_one, mul_one, mul_inv_cancel, map_one, MonoidHom.one_apply, Units.val_one, one_mul] at z1 z2
  rw [e1, e2, e3, e4, z1, z2, hA] at hE
  have hκ' : ((κ : ℂ) / 2) ≠ 0 := by
    have : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ.ne'
    exact div_ne_zero this two_ne_zero
  unfold lamE
  rw [GlobalTheory.CompanionTheory.LanglandsConstant.gam_one_half, GlobalTheory.CompanionTheory.LanglandsConstant.gam_one_half, one_mul, div_one]
  have : ((κ : ℂ) / 2 * localZeta g η (1 / 2)) * (γ - gam χ η (1 / 2)) = 0 := by
    linear_combination hE
  rcases mul_eq_zero.1 this with h | h
  · exact absurd h (mul_ne_zero hκ' hB)
  · exact sub_eq_zero.1 h

end GlobalTheory.CompanionTheory.GaussLam
