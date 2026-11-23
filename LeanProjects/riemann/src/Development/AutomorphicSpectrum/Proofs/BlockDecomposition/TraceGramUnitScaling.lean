import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HypOneZeroZero
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalGramFiberRankOneSetFormula
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension

noncomputable section

namespace GlobalTheory.CompanionTheory.AvgFree.Dilate

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

theorem gramR_dilate {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (u : R ⊗[F] E)
    (X : Fin 1 → Fin M → R ⊗[F] E) :
    gramR R σ J (fun p k => u * X p k) 0 0 = (u * sigR R σ u) * gramR R σ J X 0 0 := by
  simp only [gramR, HeckeCharacterZeroLocus.SiegelWeilU.hR, hform, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem half_trace_dilate : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)) (u : Fv F v ⊗[F] E) (X : Fin 1 → Fin M → Fv F v ⊗[F] E), (fun X : Fin 1 → Fin M → Fv F v ⊗[F] E => algebraMap F (Fv F v) (1 / 2) * Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (gramR (Fv F v) σ J X 0 0)) ((fun (X : Fin 1 → Fin M → Fv F v ⊗[F] E) (p : Fin 1) (k : Fin M) => (u : Fv F v ⊗[F] E) * X p k) X) = Algebra.norm (Fv F v) u * (fun X : Fin 1 → Fin M → Fv F v ⊗[F] E => algebraMap F (Fv F v) (1 / 2) * Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (gramR (Fv F v) σ J X 0 0)) X := by
  intro F E _ _ _ _ _ σ hσ M J hJ v u X
  beta_reduce
  have hX := GlobalTheory.CompanionTheory.SW.FibreRatio.gram_entry (Fv F v) hσ hJ X
  set r := algebraMap F (Fv F v) (1 / 2) *
    Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (gramR (Fv F v) σ J X 0 0) with hr
  have hY : gramR (Fv F v) σ J (fun p k => u * X p k) 0 0 =
      (Algebra.norm (Fv F v) u * r) ⊗ₜ[F] (1 : E) := by
    have hN : algebraMap (Fv F v) (Fv F v ⊗[F] E) (Algebra.norm (Fv F v) u) = u * sigR (Fv F v) σ u :=
      GlobalTheory.Doubling.algebraMap_norm_eq hσ u
    rw [gramR_dilate, ← hN, hX,
      Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul]
    simp
  rw [hY]
  exact GlobalTheory.CompanionTheory.SW.FibreRatio.half_trace_tmul (Fv F v) hσ _

end GlobalTheory.CompanionTheory.AvgFree.Dilate
