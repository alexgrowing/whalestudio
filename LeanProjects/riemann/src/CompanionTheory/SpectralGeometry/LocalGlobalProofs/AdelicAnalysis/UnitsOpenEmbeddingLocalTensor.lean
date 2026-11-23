import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorInvolutionAlgebraPropertiesStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.KUnits

theorem continuousOn_ringInverse {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    (h : IsOpenEmbedding (Units.val : Rˣ → R)) :
    ContinuousOn (Ring.inverse : R → R) {r | IsUnit r} := by
  rintro _ ⟨u, rfl⟩
  refine ContinuousAt.continuousWithinAt ?_
  refine (h.continuousAt_iff).1 ?_
  have : (Ring.inverse ∘ (Units.val : Rˣ → R)) = fun u : Rˣ => ((u⁻¹ : Rˣ) : R) := by
    funext v
    simp
  rw [this]
  exact (Units.continuous_val.comp continuous_inv).continuousAt

theorem units_val_isOpenEmbedding : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R]
    [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R →
    IsOpenEmbedding (Units.val : (R ⊗[F] E)ˣ → R ⊗[F] E) := by
  intro F E _ _ _ _ _ σ hσ R _ _ _ _ _ hR
  obtain ⟨hTR, hLC, hSC, hT2, hArt, hRd, hUo, -⟩ := hR
  haveI := hTR
  haveI := hLC
  haveI := hSC
  haveI := hT2
  haveI := hArt
  haveI := hRd
  obtain ⟨-, -, -, hinv, -, hfix, hunit⟩ := GlobalTheory.T.tensor_involution_algebra_properties F E σ hσ R
  obtain ⟨hTK, -, -, -, hsc, htr, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ R
  haveI := hTK
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousSMul R (R ⊗[F] E) := IsModuleTopology.toContinuousSMul R (R ⊗[F] E)
  have hfin : Module.finrank F E = 2 := hσ.2.2.1
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by omega)
  let b : Module.Basis (Fin 2) F E := Module.finBasisOfFinrankEq F E hfin
  let N : R ⊗[F] E → R := fun y =>
    algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (y * sigR R σ y)
  have hNc : Continuous N :=
    continuous_const.mul (htr.comp (continuous_id.mul hsc))
  have hhalf : algebraMap F R (1 / 2) * (2 : R) = 1 := by
    have : algebraMap F R (1 / 2) * algebraMap F R 2 = 1 := by
      rw [← map_mul]
      norm_num
    rwa [map_ofNat] at this
  have hnorm : ∀ y : R ⊗[F] E, y * sigR R σ y = N y ⊗ₜ[F] (1 : E) := by
    intro y
    obtain ⟨r, hr⟩ := hfix (y * sigR R σ y) (by rw [map_mul, hinv, mul_comm])
    have htrace : Algebra.trace R (R ⊗[F] E) (r ⊗ₜ[F] (1 : E)) = 2 * r := by
      have h1 : (r ⊗ₜ[F] (1 : E) : R ⊗[F] E) = algebraMap R (R ⊗[F] E) r := by
        simp [Algebra.TensorProduct.algebraMap_apply]
      rw [h1, Algebra.trace_algebraMap_of_basis (Algebra.TensorProduct.basis R b) r]
      simp [two_mul, two_nsmul]
    have hNr : N y = r := by
      show algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (y * sigR R σ y) = r
      rw [hr, htrace, ← mul_assoc, hhalf, one_mul]
    rw [hNr, hr]
  have hiff : ∀ y : R ⊗[F] E, IsUnit y ↔ IsUnit (N y) := by
    intro y
    constructor
    · intro hy
      have h1 : IsUnit (y * sigR R σ y) := hy.mul (hy.map (sigR R σ))
      rw [hnorm y] at h1
      exact (hunit _).1 h1
    · intro hy
      have h1 : IsUnit (y * sigR R σ y) := by
        rw [hnorm y]
        exact (hunit _).2 hy
      exact isUnit_of_mul_isUnit_left h1
  have hone : Continuous fun r : R => (r ⊗ₜ[F] (1 : E) : R ⊗[F] E) := by
    have h1 : (fun r : R => (r ⊗ₜ[F] (1 : E) : R ⊗[F] E)) = fun r : R => r • (1 : R ⊗[F] E) := by
      funext r
      simp [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul']
    rw [h1]
    exact Continuous.smul (f := fun r : R => r) (g := fun _ => (1 : R ⊗[F] E)) continuous_id continuous_const
  let f : R ⊗[F] E → R ⊗[F] E := fun y => sigR R σ y * (Ring.inverse (N y) ⊗ₜ[F] (1 : E))
  have hfc : ContinuousOn f {y | IsUnit y} := by
    have h1 : ContinuousOn (fun y => Ring.inverse (N y)) {y : R ⊗[F] E | IsUnit y} :=
      (continuousOn_ringInverse hUo).comp hNc.continuousOn (fun y hy => (hiff y).1 hy)
    exact hsc.continuousOn.mul (hone.comp_continuousOn h1)
  have hfu : ∀ u : (R ⊗[F] E)ˣ, f u.1 = ((u⁻¹ : (R ⊗[F] E)ˣ) : R ⊗[F] E) := by
    intro u
    symm
    refine Units.inv_eq_of_mul_eq_one_right ?_
    have hu : IsUnit (N u.1) := (hiff _).1 u.isUnit
    show u.1 * (sigR R σ u.1 * (Ring.inverse (N u.1) ⊗ₜ[F] (1 : E))) = 1
    rw [← mul_assoc, hnorm, Algebra.TensorProduct.tmul_mul_tmul, Ring.mul_inverse_cancel _ hu,
      mul_one]
    rfl
  refine ⟨Units.isEmbedding_val_mk' hfc hfu, ?_⟩
  have hrange : Set.range (Units.val : (R ⊗[F] E)ˣ → R ⊗[F] E) =
      N ⁻¹' Set.range (Units.val : Rˣ → R) := by
    ext y
    constructor
    · rintro ⟨u, rfl⟩
      exact (hiff _).1 u.isUnit
    · intro hy
      exact (hiff y).2 hy
  rw [hrange]
  exact hUo.isOpen_range.preimage hNc

end GlobalTheory.CompanionTheory.SW.KUnits
