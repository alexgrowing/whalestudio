import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.Fact

theorem continuous_consTup {K : Type} [Zero K] [One K] [TopologicalSpace K] (n M : ℕ) :
    Continuous (fun X : Fin n → Fin M → K => (consTup X : Fin (n + 1) → Fin (M + 1) → K)) := by
  refine continuous_pi fun a => continuous_pi fun i => ?_
  refine Fin.cases ?_ (fun a => ?_) a
  · exact continuous_const
  · refine Fin.cases ?_ (fun i => ?_) i
    · exact continuous_const
    · exact (continuous_apply i).comp (continuous_apply a)

theorem measurable_actW_consTup : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (g : HA R σ J), Measurable (fun X : Fin n → Fin M → R ⊗[F] E => actW R σ J g (consTup X)) := by
  intro F E _ _ _ _ _ σ hCM R _ _ _ _ _ hR n M J g
  obtain ⟨h1, h2, h3, h4, -⟩ := hR
  have hk := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM R
  haveI : IsTopologicalRing (R ⊗[F] E) := hk.1
  haveI : BorelSpace (Fin n → Fin M → R ⊗[F] E) := hk.2.2.2.2.2.2.2.1 n M
  haveI : BorelSpace (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) := hk.2.2.2.2.2.2.2.1 (n + 1) (M + 1)
  have hc : Continuous (fun X : Fin n → Fin M → R ⊗[F] E => actW R σ J g (consTup X)) := by
    refine continuous_pi fun a => continuous_pi fun i => ?_
    simp only [actW, actTup, Matrix.mulVec, dotProduct]
    refine continuous_finset_sum _ fun j _ => continuous_const.mul ?_
    exact (continuous_apply j).comp ((continuous_apply a).comp (continuous_consTup n M))
  exact hc.measurable

end GlobalTheory.CompanionTheory.SW.Fact
