import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.SquareIntegrable.SSmooth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TemperedBoundGL2
import GroundTheory.LocalFields.QuadraticAbelian.WeilRepQuadratic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSmoothCharCompNorm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WcEqZero
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.DualHol
open GlobalTheory.CompanionTheory.WcB
open scoped Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.GaussAvg

open GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep

theorem continuous_circle_coe : Continuous (fun z : Circle => (z : ℂ)) := by fun_prop

section Abstract

variable {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

theorem integral_subgroup_char_eq_zero (μ : Measure G) [μ.IsAddHaarMeasure] (M : AddSubgroup G)
    (hMo : IsOpen (M : Set G)) (g : G → Circle)
    (hg : ∀ r s, g (r + s) = g r * g s) {r₀ : G} (hr₀ : r₀ ∈ M) (hne : g r₀ ≠ 1) :
    ∫ r in (M : Set G), (g r : ℂ) ∂μ = 0 := by
  have hMm : MeasurableSet (M : Set G) := hMo.measurableSet
  let h : G → ℂ := (M : Set G).indicator fun r => (g r : ℂ)
  have e1 : ∫ r in (M : Set G), (g r : ℂ) ∂μ = ∫ r, h r ∂μ :=
    (integral_indicator hMm).symm
  have e2 : ∀ r, h (r + r₀) = (g r₀ : ℂ) * h r := by
    intro r
    by_cases hr : r ∈ M
    · have hr' : r + r₀ ∈ M := M.add_mem hr hr₀
      simp only [h, Set.indicator_of_mem (show r + r₀ ∈ (M : Set G) from hr'),
        Set.indicator_of_mem (show r ∈ (M : Set G) from hr), hg, Circle.coe_mul]
      ring
    · have hr' : r + r₀ ∉ M := fun hh => hr ((M.add_mem_cancel_right hr₀).1 hh)
      simp only [h, Set.indicator_of_notMem (show r + r₀ ∉ (M : Set G) from hr'),
        Set.indicator_of_notMem (show r ∉ (M : Set G) from hr), mul_zero]
  have e3 : ∫ r, h r ∂μ = (g r₀ : ℂ) * ∫ r, h r ∂μ := by
    conv_lhs => rw [← integral_add_right_eq_self h r₀]
    simp_rw [e2]
    exact integral_const_mul _ _
  rw [e1]
  exact GroundTheory.LocalField.eq_zero_of_eq_mul_of_ne_one
    (fun h' => hne (Circle.coe_eq_one.mp h')) e3

theorem integral_eq_setIntegral_of_shift (μ : Measure G) [μ.IsAddHaarMeasure] [SFinite μ]
    (M : AddSubgroup G) (hMc : IsCompact (M : Set G)) (hMo : IsOpen (M : Set G))
    (f : G → ℂ) (hf : Integrable f μ) (θ : G → G → Circle)
    (hθc : Continuous (Function.uncurry θ)) (hθa : ∀ u r s, θ u (r + s) = θ u r * θ u s)
    (hsh : ∀ r ∈ M, ∀ u, f (u + r) = f u * (θ u r : ℂ)) :
    ∫ u, f u ∂μ = ∫ u in {u : G | ∀ r ∈ M, θ u r = 1}, f u ∂μ := by
  have hMm : MeasurableSet (M : Set G) := hMo.measurableSet
  have hfin : μ (M : Set G) ≠ ⊤ := hMc.measure_lt_top.ne
  have hpos0 : μ (M : Set G) ≠ 0 :=
    (hMo.measure_pos μ ⟨0, M.zero_mem⟩).ne'
  have hreal : (μ.real (M : Set G)) ≠ 0 := by
    rw [measureReal_def]
    exact (ENNReal.toReal_pos hpos0 hfin).ne'
  set A : Set G := {u : G | ∀ r ∈ M, θ u r = 1} with hA
  have hAc : IsClosed A := by
    simp only [hA, Set.setOf_forall]
    refine isClosed_iInter fun r => isClosed_iInter fun _ => isClosed_eq ?_ continuous_const
    exact hθc.comp (continuous_id.prodMk continuous_const)
  set ν : Measure G := μ.restrict (M : Set G) with hν
  haveI : IsFiniteMeasure ν := ⟨by simpa [hν] using hMc.measure_lt_top⟩
  have hνuniv : ν.real Set.univ = μ.real (M : Set G) := by
    simp [hν, measureReal_def]
  have hI : ∀ u, ∫ r, (θ u r : ℂ) ∂ν = A.indicator (fun _ => (μ.real (M : Set G) : ℂ)) u := by
    intro u
    by_cases hu : u ∈ A
    · rw [Set.indicator_of_mem hu]
      have : ∀ᵐ r ∂ν, (θ u r : ℂ) = 1 := by
        filter_upwards [ae_restrict_mem hMm] with r hr
        rw [hu r hr]
        simp
      rw [integral_congr_ae this, integral_const, hνuniv]
      simp
    · rw [Set.indicator_of_notMem hu]
      simp only [hA, Set.mem_setOf_eq, not_forall] at hu
      obtain ⟨r₀, hr₀, hne⟩ := hu
      exact integral_subgroup_char_eq_zero μ M hMo (θ u) (hθa u) hr₀ hne
  have hint : Integrable (Function.uncurry fun u r => f u * (θ u r : ℂ)) (μ.prod ν) := by
    have h1 : Integrable (fun p : G × G => f p.1) (μ.prod ν) := hf.comp_fst ν
    have h2 : Continuous fun p : G × G => (θ p.1 p.2 : ℂ) :=
      continuous_circle_coe.comp hθc
    have h3 := h1.bdd_mul (c := 1) h2.aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => (Circle.norm_coe _).le)
    refine h3.congr (Filter.Eventually.of_forall fun p => ?_)
    simp [Function.uncurry, mul_comm]
  have step1 : ∫ r, ∫ u, f u * (θ u r : ℂ) ∂μ ∂ν = (μ.real (M : Set G) : ℂ) * ∫ u, f u ∂μ := by
    have : ∀ᵐ r ∂ν, ∫ u, f u * (θ u r : ℂ) ∂μ = ∫ u, f u ∂μ := by
      filter_upwards [ae_restrict_mem hMm] with r hr
      have e : ∀ u, f u * (θ u r : ℂ) = f (u + r) := fun u => (hsh r hr u).symm
      simp_rw [e]
      exact integral_add_right_eq_self f r
    rw [integral_congr_ae this, integral_const, hνuniv]
    simp
  have step2 : ∫ u, ∫ r, f u * (θ u r : ℂ) ∂ν ∂μ =
      (μ.real (M : Set G) : ℂ) * ∫ u in A, f u ∂μ := by
    have e : ∀ u, ∫ r, f u * (θ u r : ℂ) ∂ν =
        A.indicator (fun u => (μ.real (M : Set G) : ℂ) * f u) u := by
      intro u
      rw [integral_const_mul, hI]
      by_cases hu : u ∈ A
      · simp only [Set.indicator_of_mem hu]
        ring
      · simp only [Set.indicator_of_notMem hu, mul_zero]
    simp_rw [e]
    rw [integral_indicator hAc.measurableSet, integral_const_mul]
  have key := integral_integral_swap hint
  rw [step1.symm.symm] at key
  rw [step2] at key
  have hne : (μ.real (M : Set G) : ℂ) ≠ 0 := by exact_mod_cast hreal
  exact (mul_left_cancel₀ hne key.symm)

end Abstract

section Quadratic

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E] [Algebra.IsSeparable F E]
  [Fact (Module.finrank F E = 2)]

theorem continuous_traceForm : Continuous (Algebra.trace F E) := by
  haveI := GroundTheory.LocalField.isModuleTopology F E
  exact IsModuleTopology.continuous_of_linearMap (Algebra.trace F E)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [ValuativeExtension F E] in
theorem norm_eq_trace_mul {c : E} (hc : Algebra.trace F E c = 1) (u : E) :
    Algebra.norm F u = Algebra.trace F E (c * (u * conj F E u)) := by
  rw [← algebraMap_norm_eq_mul_conj, mul_comm c, ← Algebra.smul_def, map_smul, hc, smul_eq_mul,
    mul_one]

theorem continuous_normForm : Continuous (Algebra.norm F : E → F) := by
  obtain ⟨c, hc⟩ := Algebra.trace_surjective F E 1
  have e : (Algebra.norm F : E → F) = fun u => Algebra.trace F E (c * (u * conj F E u)) :=
    funext (norm_eq_trace_mul hc)
  rw [e]
  exact continuous_traceForm.comp (continuous_const.mul (continuous_id.mul continuous_conj))

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [ValuativeExtension F E] in

theorem phase_add (κ : F) (ξ u r : E) :
    κ * Algebra.norm F (u + r) - Algebra.trace F E (ξ * (u + r)) =
      (κ * Algebra.norm F u - Algebra.trace F E (ξ * u)) + κ * Algebra.norm F r +
        Algebra.trace F E ((algebraMap F E κ * conj F E u - ξ) * r) := by
  have ht : Algebra.trace F E (u * conj F E r) = Algebra.trace F E (conj F E u * r) := by
    rw [← trace_conj (K := F) (u * conj F E r), map_mul, conj_conj]
  have h2 : Algebra.trace F E ((algebraMap F E κ * conj F E u - ξ) * r) =
      κ * Algebra.trace F E (conj F E u * r) - Algebra.trace F E (ξ * r) := by
    rw [sub_mul, map_sub, mul_assoc, ← Algebra.smul_def, map_smul, smul_eq_mul]
  rw [norm_add, h2, mul_add ξ, map_add, ht]
  ring

end Quadratic

theorem gaussI_eq_setIntegral : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E] [Algebra.IsSeparable F E] [Fact (Module.finrank F E = 2)] (χ : AddChar F Circle), Continuous χ → ∀ σ : E ≃ₐ[F] E, σ ≠ AlgEquiv.refl → ∀ (μ : Measure E) [μ.IsAddHaarMeasure] (Φ : E → ℂ), IsLocallyConstant Φ → HasCompactSupport Φ → ∀ (κ : F) (ξ : E) (M : AddSubgroup E), IsCompact (M : Set E) → IsOpen (M : Set E) → (∀ r ∈ M, ∀ u, Φ (u + r) = Φ u) → (∀ r ∈ M, χ (κ * Algebra.norm F r) = 1) → gaussI χ μ Φ κ ξ = ∫ u in {u : E | ∀ r ∈ M, χ (Algebra.trace F E ((algebraMap F E κ * σ u - ξ) * r)) = 1}, (χ (κ * Algebra.norm F u - Algebra.trace F E (ξ * u)) : ℂ) * Φ u ∂μ := by
  intro F _ _ _ _ _ _ E _ _ _ _ _ _ _ _ _ _ _ χ hχ σ hσ μ _ Φ hΦl hΦc κ ξ M hMc hMo hΦM hχM
  obtain rfl : σ = conj F E := (eq_one_or_eq_conj σ).resolve_left hσ
  have hN : Continuous (Algebra.norm F : E → F) := continuous_normForm
  have hT : Continuous (Algebra.trace F E) := continuous_traceForm
  have hph : Continuous fun u : E => χ (κ * Algebra.norm F u - Algebra.trace F E (ξ * u)) :=
    hχ.comp ((continuous_const.mul hN).sub (hT.comp (continuous_const.mul continuous_id)))
  have hfc : Continuous fun u : E =>
      (χ (κ * Algebra.norm F u - Algebra.trace F E (ξ * u)) : ℂ) * Φ u :=
    (continuous_circle_coe.comp hph).mul hΦl.continuous
  have hfi : Integrable (fun u : E =>
      (χ (κ * Algebra.norm F u - Algebra.trace F E (ξ * u)) : ℂ) * Φ u) μ :=
    hfc.integrable_of_hasCompactSupport hΦc.mul_left
  refine integral_eq_setIntegral_of_shift μ M hMc hMo _ hfi
    (fun u r => χ (Algebra.trace F E ((algebraMap F E κ * conj F E u - ξ) * r))) ?_ ?_ ?_
  · refine hχ.comp (hT.comp (Continuous.mul ?_ continuous_snd))
    exact (continuous_const.mul (continuous_conj.comp continuous_fst)).sub continuous_const
  · intro u r s
    rw [mul_add, map_add, AddChar.map_add_eq_mul]
  · intro r hr u
    beta_reduce
    rw [phase_add, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, hχM r hr, hΦM r hr, mul_one,
      Circle.coe_mul]
    ring

end GlobalTheory.CompanionTheory.GaussAvg
