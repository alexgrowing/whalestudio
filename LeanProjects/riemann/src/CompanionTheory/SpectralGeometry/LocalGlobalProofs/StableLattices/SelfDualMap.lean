import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdelesLocalRingTotallyReal
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsUnipotentInvariantCompactlySupportedWeight

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.SdAny

theorem selfDual_map {V W : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [MeasurableSpace V] [BorelSpace V] [AddCommGroup W] [TopologicalSpace W]
    [IsTopologicalAddGroup W] [MeasurableSpace W] [BorelSpace W] (e : V ≃ₜ+ W) (μ : Measure V)
    (χ : V → V → ℂ) (h : SelfDual μ χ) :
    SelfDual (μ.map e) (fun x y => χ (e.symm x) (e.symm y)) := by
  obtain ⟨hH, hinv⟩ := h
  have hemb : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding
  refine ⟨e.isAddHaarMeasure_map μ, ?_⟩
  intro Φ hc hs hint z
  let H : V → ℂ := fun y => ∫ x, Φ (e x) * χ x y ∂μ
  have h1 : ∀ y, ∫ x, Φ x * χ (e.symm x) (e.symm y) ∂(μ.map e) = H (e.symm y) := fun y => by
    rw [hemb.integral_map]
    simp [H]
  simp only [h1] at hint ⊢
  have hint2 : Integrable H μ := by
    have h2 := (hemb.integrable_map_iff).1 hint
    simpa [Function.comp_def] using h2
  have h3 := hinv (Φ ∘ e) (hc.comp e.continuous) (hs.comp_homeomorph e.toHomeomorph) hint2 (e.symm z)
  rw [hemb.integral_map]
  simp only [ContinuousAddEquiv.symm_apply_apply]
  refine h3.trans ?_
  simp

section Unit

variable {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

def evalE : (Unit → R) ≃ₜ+ R where
  toFun x := x ()
  invFun s := fun _ => s
  left_inv x := rfl
  right_inv s := rfl
  map_add' x y := rfl
  continuous_toFun := continuous_apply ()
  continuous_invFun := continuous_pi fun _ => continuous_id

variable [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R]

theorem iff_of_unit (ψR : R → ℂ) (lam : Measure R) [SigmaFinite lam] (c : ℝ≥0)
    (B : Matrix Unit Unit R) (hB : B = 1)
    (h : ∀ μ : Measure (Unit → R), SelfDual μ (fun x y => ψR (x ⬝ᵥ (B *ᵥ y))) ↔
      μ = c • Measure.pi fun _ => lam) (ν : Measure R) :
    SelfDual ν (fun s t => ψR (s * t)) ↔ ν = c • lam := by
  subst hB
  have hχ : (fun x y : Unit → R => ψR (x ⬝ᵥ ((1 : Matrix Unit Unit R) *ᵥ y))) =
      fun x y => ψR (evalE x * evalE y) := by
    funext x y
    simp [evalE, dotProduct]
  rw [hχ] at h
  have hm : Measurable (evalE : (Unit → R) ≃ₜ+ R) := evalE.continuous.measurable
  have hms : Measurable (evalE.symm : R ≃ₜ+ (Unit → R)) := evalE.symm.continuous.measurable
  have hp : (Measure.pi fun _ : Unit => lam).map evalE = lam :=
    (measurePreserving_funUnique lam Unit).map_eq
  have hmm : ∀ μ : Measure R, (μ.map evalE.symm).map evalE = μ := fun μ => by
    rw [Measure.map_map hm hms]
    convert Measure.map_id
    ext x
    simp
  constructor
  · intro hν
    have h1 := selfDual_map evalE.symm ν _ hν
    have h2 := (h _).1 h1
    have h3 := congrArg (Measure.map evalE) h2
    rw [hmm, Measure.map_smul, hp] at h3
    exact h3
  · rintro rfl
    have h1 := selfDual_map evalE _ _ ((h _).2 rfl)
    rw [Measure.map_smul, hp] at h1
    simpa using h1

end Unit

theorem selfDual_any : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (laminf : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), IsStdInf laminf → (∀ v, IsStdV v (lam v)) → ∀ ψ, IsCharAF F ψ → ∃ (cinf : ℝ≥0) (c : HeightOneSpectrum (𝓞 F) → ℝ≥0), IsUnitProd cinf c ∧ (∀ ν : Measure (Ainf F), SelfDual ν (fun s t => psiInf F ψ (s * t)) ↔ ν = cinf • laminf) ∧ ∀ v : HeightOneSpectrum (𝓞 F), ∀ ν : Measure (Fv F v), SelfDual ν (fun s t => psiV F ψ v (s * t)) ↔ ν = c v • lam v := by
  intro F E _ _ _ _ _ σ hCM laminf lam hinf hlam ψ hψ
  obtain ⟨cinf, c, hU, h1, h2⟩ := GlobalTheory.CompanionTheory.SW.SdCoord.selfDual_coord F hCM.1 laminf lam hinf hlam ψ hψ
    Unit 1 (Matrix.isSymm_one) (by simp)
  refine ⟨cinf, c, hU, fun ν => ?_, fun v ν => ?_⟩
  · obtain ⟨a1, a2, a3, a4, -, -, -, -⟩ := isLocR_Ainf F hCM.1
    haveI := a1; haveI := a2; haveI := a3; haveI := a4
    haveI : BorelSpace (Ainf F) := ⟨rfl⟩
    haveI := hinf.1
    exact iff_of_unit (psiInf F ψ) laminf cinf _ (Matrix.map_one _ (map_zero _) (map_one _)) h1 ν
  · obtain ⟨a1, a2, a3, a4, -, -, -, -⟩ := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
    haveI := a1; haveI := a2; haveI := a3; haveI := a4
    haveI : BorelSpace (Fv F v) := ⟨rfl⟩
    haveI := (hlam v).1
    exact iff_of_unit (psiV F ψ v) (lam v) (c v) _ (Matrix.map_one _ (map_zero _) (map_one _)) (h2 v) ν

end GlobalTheory.CompanionTheory.SW.SdAny
