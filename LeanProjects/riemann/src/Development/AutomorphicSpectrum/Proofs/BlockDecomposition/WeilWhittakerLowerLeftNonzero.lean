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

noncomputable section

namespace GlobalTheory.CompanionTheory.WS

theorem model_ne : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (χ : AddChar F Circle), IsStd χ → ∀ Φ : F × F → ℂ, GlobalTheory.CompanionTheory.WS.IsSB Φ → ∀ g : GL (Fin 2) F, g.val 1 0 ≠ 0 → ∀ u : Fˣ, GL2LocalData.rW χ GL2LocalData.swapE ((selfDualMeasure χ).prod (selfDualMeasure χ)) 1 (g.val 0 0 / (g.val).det) (g.val 0 1) (g.val 1 0 / (g.val).det) (g.val 1 1) (fun x => Φ (x * ((g.val).det, 1))) ((u : F), ((u⁻¹ : Fˣ) : F)) = mp u 1 * GlobalTheory.CompanionTheory.WS.inn χ (GlobalTheory.CompanionTheory.WS.pF χ Φ ∘ GlobalTheory.CompanionTheory.WS.rowAct g) u := by
  intro F _ _ _ _ _ _ χ hχ Φ hΦ g hc u
  have hd0 : (g.val).det ≠ 0 := (Matrix.isUnits_det_units g).ne_zero
  have hdet : (g.val).det = g.val 0 0 * g.val 1 1 - g.val 0 1 * g.val 1 0 := Matrix.det_fin_two _
  rw [GlobalTheory.CompanionTheory.WcSplit.rW_lower hχ hΦ.1 hΦ.2 hc hdet hd0 u]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [Function.comp_apply, rowAct, pF, GlobalTheory.CompanionTheory.WcSplit.phiW, Matrix.cons_val_zero, Matrix.cons_val_one]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [mul_comm t]

end GlobalTheory.CompanionTheory.WS
