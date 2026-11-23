import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HypOneZeroZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitScalingRankOneVolumeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TraceGramUnitScalingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GlobalUnitScalingHaarProductFormula
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.DiagonalPhaseFirstVector
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TensTop
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

noncomputable section
namespace GlobalTheory.CompanionTheory.WeilSiegel.DilPush

theorem push_dil : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 1 ≤ M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), IsStdV v lam → ∀ (P : Set (Fin 1 → Fin M → Fv F v ⊗[F] E)) (c : ℝ≥0), MeasurableSet P → (∀ S : Set (Fv F v), MeasurableSet S → coordW (Fv F v) b lam 1 M (P ∩ (fun X : Fin 1 → Fin M → Fv F v ⊗[F] E => algebraMap F (Fv F v) (1 / 2) * Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (gramR (Fv F v) σ J X 0 0)) ⁻¹' S) ≤ (c : ℝ≥0∞) * lam S) → ∀ (u : (Fv F v ⊗[F] E)ˣ) (S : Set (Fv F v)), MeasurableSet S → coordW (Fv F v) b lam 1 M ((fun (X : Fin 1 → Fin M → Fv F v ⊗[F] E) (p : Fin 1) (k : Fin M) => (u : Fv F v ⊗[F] E) * X p k) '' P ∩ (fun X : Fin 1 → Fin M → Fv F v ⊗[F] E => algebraMap F (Fv F v) (1 / 2) * Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (gramR (Fv F v) σ J X 0 0)) ⁻¹' S) ≤ ((c * ‖Algebra.norm (Fv F v) (u : Fv F v ⊗[F] E)‖₊ ^ (M - 1) : ℝ≥0) : ℝ≥0∞) * lam S := by
  intro F E _ _ _ _ _ σ hσ M J hJ hM d b v lam hlam P c hP hbound u S hS
  haveI : FiniteDimensional F E := Module.Finite.of_basis b
  haveI := hlam.1
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  set Q : (Fin 1 → Fin M → Fv F v ⊗[F] E) → Fv F v := fun X => algebraMap F (Fv F v) (1 / 2) * Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (gramR (Fv F v) σ J X 0 0) with hQ
  set D : (Fin 1 → Fin M → Fv F v ⊗[F] E) → (Fin 1 → Fin M → Fv F v ⊗[F] E) := fun X p k => (u : Fv F v ⊗[F] E) * X p k with hD
  set n : Fv F v := Algebra.norm (Fv F v) (u : Fv F v ⊗[F] E) with hn
  have hn0 : n ≠ 0 := (u.isUnit.map (Algebra.norm (Fv F v))).ne_zero
  have hdil : ∀ X, Q (D X) = n * Q X := fun X => GlobalTheory.T.trace_gram_unit_scaling F E σ hσ M J hJ v u X
  set S' : Set (Fv F v) := (fun t => n * t) ⁻¹' S with hS'def
  have hmul : Measurable (fun t : Fv F v => n * t) := (continuous_const_mul n).measurable
  have hS' : MeasurableSet S' := hmul hS
  have hset : D '' P ∩ Q ⁻¹' S = D '' (P ∩ Q ⁻¹' S') := by
    ext Y
    constructor
    · rintro ⟨⟨X, hX, rfl⟩, hY⟩
      refine ⟨X, ⟨hX, ?_⟩, rfl⟩
      show n * Q X ∈ S
      rw [← hdil]
      exact hY
    · rintro ⟨X, ⟨hX, hXS⟩, rfl⟩
      refine ⟨⟨X, hX, rfl⟩, ?_⟩
      show Q (D X) ∈ S
      rw [hdil]
      exact hXS
  have hQc : Continuous Q := by
    have h1 : Continuous (Algebra.trace (Fv F v) (Fv F v ⊗[F] E)) :=
      PI.VolStabSW.SdUniqW.continuous_trace_tens (F := F) (E := E) (Fv F v)
    have h2 : Continuous fun X : Fin 1 → Fin M → Fv F v ⊗[F] E => gramR (Fv F v) σ J X 0 0 :=
      (continuous_apply_apply 0 0).comp (PI.VolStabS.continuous_gramR (Fv F v) σ J)
    exact continuous_const.mul (h1.comp h2)
  have hQm : Measurable Q := hQc.measurable
  have hlamS : lam S' = (‖n‖₊ : ℝ≥0∞)⁻¹ * lam S := by
    have h := GlobalTheory.CompanionTheory.SW.ProdFormula.map_mul_left_finite v n hn0 lam hlam.1
    have h2 := congrArg (fun μ : Measure (Fv F v) => μ S) h
    simp only [Measure.smul_apply] at h2
    rw [Measure.map_apply hmul hS] at h2
    rw [hS'def, h2, ENNReal.smul_def, smul_eq_mul]
    simp [ENNReal.coe_inv (nnnorm_ne_zero_iff.2 hn0)]
  rw [hset, GlobalTheory.T.unit_scaling_rank_one_volume F E σ hσ M d b v lam hlam u _ (hP.inter (hQm hS'))]
  set a : ℝ≥0∞ := (‖n‖₊ : ℝ≥0∞) with ha
  have ha0 : a ≠ 0 := by simpa [ha] using hn0
  have hat : a ≠ ⊤ := ENNReal.coe_ne_top
  have hpow : a ^ M = a ^ (M - 1) * a := by rw [← pow_succ, Nat.sub_add_cancel hM]
  have haa : a * a⁻¹ = 1 := ENNReal.mul_inv_cancel ha0 hat
  calc a ^ M * coordW (Fv F v) b lam 1 M (P ∩ Q ⁻¹' S')
      ≤ a ^ M * ((c : ℝ≥0∞) * lam S') := by gcongr; exact hbound S' hS'
    _ = (c : ℝ≥0∞) * a ^ (M - 1) * (a * a⁻¹) * lam S := by rw [hlamS, hpow]; ring
    _ = ((c * ‖n‖₊ ^ (M - 1) : ℝ≥0) : ℝ≥0∞) * lam S := by rw [haa, ha]; push_cast; ring

end GlobalTheory.CompanionTheory.WeilSiegel.DilPush
