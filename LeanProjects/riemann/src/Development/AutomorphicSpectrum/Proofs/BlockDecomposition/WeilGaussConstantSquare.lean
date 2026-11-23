import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GTil
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel NNReal ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.GaussLam.Left

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E] [Algebra.IsSeparable F E]
  [Fact (Module.finrank F E = 2)]

theorem continuous_gal (τ : E ≃ₐ[F] E) : Continuous τ := by
  rcases GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.eq_one_or_eq_conj τ with rfl | rfl
  · exact continuous_id
  · exact GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.continuous_conj

theorem comp_norm_mem {f : F → ℂ} (hf : f ∈ schwartzBruhat F) :
    (fun x : E => f (Algebra.norm F x)) ∈ schwartzBruhat E := by
  obtain ⟨N, M, -, hM⟩ := exists_invariant_of_mem_schwartzBruhat hf
  refine ⟨hf.1.comp_continuous (continuous_algebraNorm F E), ?_⟩
  refine HasCompactSupport.intro (isCompact_valBall (min M 0)) fun x hx => ?_
  by_contra h0
  apply hx
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hx (zero_mem _)
  have hN0 : Algebra.norm F x ≠ 0 := Algebra.norm_ne_zero_iff.2 hx0
  have h1 := (mem_valBall_iff_le_ord hN0).1 (hM _ h0)
  rw [ord_norm (K := F) (L := E)] at h1
  have hd : (1 : ℤ) ≤ residueDegree F E := by exact_mod_cast residueDegree_pos F E
  show x ∈ valBall E (min M 0)
  rw [mem_valBall_iff_le_ord hx0]
  by_contra hlt
  push_neg at hlt
  have h2 : ord x < 0 := lt_of_lt_of_le hlt (min_le_right _ _)
  have h3 : ord x < M := lt_of_lt_of_le hlt (min_le_left _ _)
  nlinarith

theorem fts_mem [MeasurableSpace E] [BorelSpace E] {ψ : AddChar E Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
    (μ : Measure E) [μ.IsAddHaarMeasure] (σ : E ≃ₐ[F] E) {Φ : E → ℂ} (hΦ : Φ ∈ schwartzBruhat E) :
    (fun u => localFourier μ ψ Φ (σ u)) ∈ schwartzBruhat E := by
  have h := localFourier_mem_schwartzBruhat μ hψ hψ1 hΦ
  let e : E ≃ₜ E := ⟨σ.toEquiv, continuous_gal σ, continuous_gal σ.symm⟩
  exact ⟨h.1.comp_continuous e.continuous, h.2.comp_homeomorph e⟩

theorem real_apply_eq_actE_real_inv_mul [MeasurableSpace F] [BorelSpace F] [MeasurableSpace E] [BorelSpace E]
    (χ : AddChar F Circle) (hχ : Continuous χ) (hχ1 : χ ≠ 1) (σ : E ≃ₐ[F] E) {Φ : E → ℂ}
    (hΦ : Φ ∈ SBE E) {g : F → ℂ} (hg : g ∈ schwartzBruhat F) :
    ∫ a, g a * ∫ u, (χ (a * Algebra.norm F u) : ℂ) * FTE E χ σ Φ u ∂muE E χ ∂selfDualMeasure χ =
      ∫ z, Φ z * localFourier (muE E χ) (chE E χ)
        (fun x : E => localFourier (selfDualMeasure χ) χ g (Algebra.norm F x)) (σ.symm z) ∂muE E χ := by
  have hχE : Continuous (chE E χ) := continuous_traceChar hχ hχ1
  have hχE1 : chE E χ ≠ 1 := traceChar_ne_one hχ hχ1
  have hΦ' : Φ ∈ schwartzBruhat E := hΦ
  have hc : Continuous fun x : F => (χ x : ℂ) := continuous_subtype_val.comp hχ
  have hcE : Continuous fun x : E => (chE E χ x : ℂ) := continuous_subtype_val.comp hχE
  have hN : Continuous (Algebra.norm F : E → F) := continuous_algebraNorm F E
  obtain ⟨T, hT⟩ : ∃ T, T = FTE E χ σ Φ := ⟨_, rfl⟩
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : E → ℂ, Ψ = fun x => localFourier (selfDualMeasure χ) χ g (Algebra.norm F x) :=
    ⟨_, rfl⟩
  rw [← hT, ← hΨ]
  have hTu : ∀ u, T u = ∫ z, Φ z * (chE E χ (σ u * z) : ℂ) ∂muE E χ := fun u => by rw [hT]; rfl
  have hTe : T = fun u => localFourier (muE E χ) (chE E χ) Φ (σ u) := by
    funext u
    rw [hTu, localFourier]
    simp only [mul_comm (σ u)]
  have hTsb : T ∈ schwartzBruhat E := hTe ▸ fts_mem hχE hχE1 _ σ hΦ'
  have hΨsb : Ψ ∈ schwartzBruhat E :=
    hΨ ▸ comp_norm_mem (localFourier_mem_schwartzBruhat _ hχ hχ1 hg)
  have hgi := integrable_of_mem_schwartzBruhat (selfDualMeasure χ) hg
  have hTi := integrable_of_mem_schwartzBruhat (muE E χ) hTsb
  have hΦi := integrable_of_mem_schwartzBruhat (muE E χ) hΦ'
  have hΨi := integrable_of_mem_schwartzBruhat (muE E χ) hΨsb
  have s1 : ∫ a, g a * ∫ u, (χ (a * Algebra.norm F u) : ℂ) * T u ∂muE E χ ∂selfDualMeasure χ =
      ∫ u, T u * Ψ u ∂muE E χ := by
    let G : F → E → ℂ := fun a u => g a * ((χ (a * Algebra.norm F u) : ℂ) * T u)
    have hG : Integrable (Function.uncurry G) ((selfDualMeasure χ).prod (muE E χ)) := by
      have hdom := hgi.norm.mul_prod hTi.norm
      refine hdom.mono' ?_ (Filter.Eventually.of_forall fun p => ?_)
      · refine Continuous.aestronglyMeasurable ?_
        exact (hg.1.continuous.comp continuous_fst).mul
          ((hc.comp (continuous_fst.mul (hN.comp continuous_snd))).mul
            (hTsb.1.continuous.comp continuous_snd))
      · simp [G, Function.uncurry, Circle.norm_coe]
    calc ∫ a, g a * ∫ u, (χ (a * Algebra.norm F u) : ℂ) * T u ∂muE E χ ∂selfDualMeasure χ
        = ∫ a, ∫ u, G a u ∂muE E χ ∂selfDualMeasure χ := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
          exact (integral_const_mul _ _).symm
      _ = ∫ u, ∫ a, G a u ∂selfDualMeasure χ ∂muE E χ := integral_integral_swap hG
      _ = ∫ u, T u * Ψ u ∂muE E χ := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
          show ∫ a, G a u ∂selfDualMeasure χ = T u * Ψ u
          rw [hΨ]
          show _ = T u * ∫ a, g a * (χ (a * Algebra.norm F u) : ℂ) ∂selfDualMeasure χ
          rw [← integral_const_mul]
          refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
          show g a * ((χ (a * Algebra.norm F u) : ℂ) * T u) = _
          ring
  have s2 : ∫ u, T u * Ψ u ∂muE E χ =
      ∫ z, Φ z * localFourier (muE E χ) (chE E χ) Ψ (σ.symm z) ∂muE E χ := by
    let H : E → E → ℂ := fun u z => Φ z * (chE E χ (σ u * z) : ℂ) * Ψ u
    have hH : Integrable (Function.uncurry H) ((muE E χ).prod (muE E χ)) := by
      have hdom := hΨi.norm.mul_prod hΦi.norm
      refine hdom.mono' ?_ (Filter.Eventually.of_forall fun p => ?_)
      · refine Continuous.aestronglyMeasurable ?_
        exact ((hΦ'.1.continuous.comp continuous_snd).mul
          (hcE.comp (((continuous_gal σ).comp continuous_fst).mul continuous_snd))).mul
            (hΨsb.1.continuous.comp continuous_fst)
      · simp [H, Function.uncurry, Circle.norm_coe, mul_comm]
    calc ∫ u, T u * Ψ u ∂muE E χ = ∫ u, ∫ z, H u z ∂muE E χ ∂muE E χ := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
          show T u * Ψ u = ∫ z, Φ z * (chE E χ (σ u * z) : ℂ) * Ψ u ∂muE E χ
          rw [integral_mul_const, hTu]
      _ = ∫ z, ∫ u, H u z ∂muE E χ ∂muE E χ := integral_integral_swap hH
      _ = ∫ z, Φ z * localFourier (muE E χ) (chE E χ) Ψ (σ.symm z) ∂muE E χ := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
          show ∫ u, H u z ∂muE E χ = Φ z * ∫ u, Ψ u * (chE E χ (u * σ.symm z) : ℂ) ∂muE E χ
          rw [← integral_const_mul]
          refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
          have e : chE E χ (σ u * z) = chE E χ (u * σ.symm z) := by
            show χ (Algebra.trace F E (σ u * z)) = χ (Algebra.trace F E (u * σ.symm z))
            have e1 : σ (u * σ.symm z) = σ u * z := by rw [map_mul, AlgEquiv.apply_symm_apply]
            rw [← e1, Algebra.trace_eq_of_algEquiv]
          show Φ z * (chE E χ (σ u * z) : ℂ) * Ψ u = _
          rw [e]
          ring
  exact s1.trans s2

theorem left_average : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E] [Algebra.IsSeparable F E] [Fact (Module.finrank F E = 2)] (χ : AddChar F Circle), Continuous χ → χ ≠ 1 → ∀ σ : E ≃ₐ[F] E, ∀ Φ ∈ SBE E, ∀ g : F → ℂ, g ∈ schwartzBruhat F → ∫ a, g a * ∫ u, (χ (a * Algebra.norm F u) : ℂ) * FTE E χ σ Φ u ∂muE E χ ∂selfDualMeasure χ = ∫ z, Φ z * localFourier (muE E χ) (chE E χ) (fun x : E => localFourier (selfDualMeasure χ) χ g (Algebra.norm F x)) (σ.symm z) ∂muE E χ := by
  intro F _ _ _ _ _ _ E _ _ _ _ _ _ _ _ _ _ _ χ hχ hχ1 σ Φ hΦ g hg
  exact real_apply_eq_actE_real_inv_mul χ hχ hχ1 σ hΦ hg

end GlobalTheory.CompanionTheory.GaussLam.Left
