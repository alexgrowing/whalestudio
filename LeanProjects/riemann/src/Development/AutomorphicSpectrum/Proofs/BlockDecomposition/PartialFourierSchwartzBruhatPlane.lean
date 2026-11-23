import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetInd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactWhittakerEqGodementLocal
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open scoped NumberField.AdeleRing ValuativeRel

namespace GlobalTheory.CompanionTheory.WS.PF

theorem isSB_pF : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (χ : AddChar F Circle), IsStd χ → ∀ Φ : F × F → ℂ, GlobalTheory.CompanionTheory.WS.IsSB Φ → GlobalTheory.CompanionTheory.WS.IsSB (GlobalTheory.CompanionTheory.WS.pF χ Φ) := by
  intro F _ _ _ _ _ _ χ hχ Φ hΦ
  have hm := GodementSectionLocal.mem_schwartzBruhat2.1 (GlobalTheory.CompanionTheory.WcSplit.phiW_mem hχ hΦ.1 hΦ.2)
  have e : GlobalTheory.CompanionTheory.WS.pF χ Φ = GlobalTheory.CompanionTheory.WcSplit.phiW χ Φ ∘ (Homeomorph.finTwoArrow (X := F)).symm := by
    funext p
    simp [GlobalTheory.CompanionTheory.WS.pF, GlobalTheory.CompanionTheory.WcSplit.phiW, mul_comm]
  rw [e]
  exact ⟨hm.1.comp_continuous (Homeomorph.finTwoArrow (X := F)).symm.continuous,
    hm.2.comp_homeomorph (Homeomorph.finTwoArrow (X := F)).symm⟩

end GlobalTheory.CompanionTheory.WS.PF
