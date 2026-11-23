import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralSchwartzFamilyMemSpace
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFinsetOfEventually
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LintegralFintypeProdEqProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdemSmulUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DOpMemDStep
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.ConeEuler
open GlobalTheory.Doubling (absE absEv unitFin ideleAt)
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_schwartz_family_mem_space : ∀ {D Ω₁ Ω₂ : Type} [NormedAddCommGroup D] [NormedSpace ℝ D] [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    (m₁ : Measure Ω₁) (m₂ : Measure Ω₂) [IsFiniteMeasure m₁] [SFinite m₂] (V : Submodule ℂ (SchwartzMap D ℂ)),
    FiniteDimensional ℂ V → ∀ G : Ω₁ → Ω₂ → SchwartzMap D ℂ, (∀ k l, G k l ∈ V) →
    (∀ y, StronglyMeasurable (Function.uncurry fun k l => iteratedFDeriv ℝ 0 (⇑(G k l)) y)) →
    (∃ (C : ℝ) (w : Ω₂ → ℝ), Integrable w m₂ ∧ ∀ k l, SchwartzMap.seminorm ℂ 0 0 (G k l) ≤ C * w l) →
    ∃ g ∈ V, ⇑g = fun y => ∫ k, ∫ l, G k l y ∂m₂ ∂m₁ := by
  first | exact @GlobalTheory.fdint_mem_finiteDimensional | exact GlobalTheory.fdint_mem_finiteDimensional | (intros; apply GlobalTheory.fdint_mem_finiteDimensional <;> assumption)
