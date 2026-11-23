import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetInd
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open scoped NumberField.AdeleRing ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.WS

theorem inner_integrable : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (χ : AddChar F Circle), IsStd χ → ∀ Ψ : F × F → ℂ, GlobalTheory.CompanionTheory.WS.IsSB Ψ → ∀ u : Fˣ, Integrable (fun y : F => Ψ ((u : F), (u : F) * y) * (χ (-y) : ℂ)) (selfDualMeasure χ) := by
  intro F _ _ _ _ _ _ χ hχ Ψ hΨ u
  have hcΨ : Continuous Ψ := hΨ.1.continuous
  have hcχ : Continuous (fun y : F => ((χ (-y) : Circle) : ℂ)) :=
    (continuous_induced_dom : Continuous ((↑) : Circle → ℂ)).comp (hχ.1.comp continuous_neg)
  have hcg : Continuous (fun y : F => Ψ ((u : F), (u : F) * y)) :=
    hcΨ.comp (continuous_const.prodMk (continuous_const.mul continuous_id))
  have hK : IsCompact ((fun p : F × F => ((u⁻¹ : Fˣ) : F) * p.2) '' tsupport Ψ) :=
    hΨ.2.isCompact.image (continuous_const.mul continuous_snd)
  have hs : HasCompactSupport (fun y : F => Ψ ((u : F), (u : F) * y)) := by
    refine HasCompactSupport.intro hK (fun y hy => ?_)
    by_contra hne
    exact hy ⟨((u : F), (u : F) * y), subset_tsupport _ hne, by simp⟩
  exact (hcg.mul hcχ).integrable_of_hasCompactSupport hs.mul_right

end GlobalTheory.CompanionTheory.WS
