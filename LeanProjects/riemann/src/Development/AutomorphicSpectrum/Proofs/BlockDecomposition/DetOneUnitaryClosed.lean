import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousSingleV
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRing

noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2 GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology

namespace GlobalTheory.CompanionTheory.SaGen

theorem isClosed_det_eq_one : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ {M : ℕ} (J : Matrix (Fin M) (Fin M) E) {K : Type} [NontriviallyNormedField K] [Algebra F K], IsClosed {x : HA K σ J | ((HA.mat K σ J x).1 : Matrix (Fin M) (Fin M) (K ⊗[F] E)).det = 1} := by
  intro F E _ _ _ _ _ σ _ M J K _ _
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (K ⊗[F] E) := GlobalTheory.CompanionTheory.SW.TopK.isTopRing K
  haveI : T2Space (K ⊗[F] E) :=
    (GlobalTheory.CompanionTheory.SW.TopK.coordHomeo K (Module.finBasis F E)).isEmbedding.t2Space
  have hc : Continuous fun x : HA K σ J =>
      ((HA.mat K σ J x).1 : Matrix (Fin M) (Fin M) (K ⊗[F] E)) :=
    Units.continuous_val.comp continuous_subtype_val
  exact isClosed_eq hc.matrix_det continuous_const

end GlobalTheory.CompanionTheory.SaGen

end
