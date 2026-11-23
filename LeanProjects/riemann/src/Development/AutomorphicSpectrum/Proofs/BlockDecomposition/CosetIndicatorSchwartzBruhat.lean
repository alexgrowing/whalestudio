import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetInd
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open scoped NumberField.AdeleRing ValuativeRel

namespace GlobalTheory.CompanionTheory.WS.Coset

theorem isSB_cosetInd : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (n : ℤ) (x : F × F), GlobalTheory.CompanionTheory.WS.IsSB (GlobalTheory.CompanionTheory.WS.cosetInd n x) := by
  intro F _ _ _ _ _ _ n x
  have hB : IsClopen (valBall F n : Set F) :=
    ⟨AddSubgroup.isClosed_of_isOpen _ (isOpen_valBall n), isOpen_valBall n⟩
  have hP : IsClopen ((valBall F n : Set F) ×ˢ (valBall F n : Set F)) := hB.prod hB
  have hS : {v : F × F | v - x ∈ Ln F n} =
      (fun v : F × F => v - x) ⁻¹' ((valBall F n : Set F) ×ˢ (valBall F n : Set F)) := rfl
  have hC : IsClopen {v : F × F | v - x ∈ Ln F n} := by
    rw [hS]
    exact hP.preimage (continuous_id.sub continuous_const)
  have hK : IsCompact {v : F × F | v - x ∈ Ln F n} := by
    rw [hS]
    exact (Homeomorph.subRight x).isCompact_preimage.2
      ((isCompact_valBall n).prod (isCompact_valBall n))
  refine ⟨?_, ?_⟩
  · exact (LocallyConstant.indicator (1 : LocallyConstant (F × F) ℂ) hC).isLocallyConstant
  · exact HasCompactSupport.intro hK fun v hv => Set.indicator_of_notMem hv _

end GlobalTheory.CompanionTheory.WS.Coset
