import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeFormsMapInjective
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraMapConeRing
open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cone_forms_map_injective : ∀ {K : Type} [Field K] {n d : ℕ} (S : Finset (Fin d)) (a : ℕ), Function.Injective (omMap (K := K) (incl (le_top : (cone S : AddSubmonoid (Gam n d)) ≤ ⊤)) a) := by
  first | exact @GlobalTheory.CompanionTheory.SurjectionOntoH4.OmlInj.omMap_incl_injective | exact GlobalTheory.CompanionTheory.SurjectionOntoH4.OmlInj.omMap_incl_injective | (intros; apply GlobalTheory.CompanionTheory.SurjectionOntoH4.OmlInj.omMap_incl_injective <;> assumption)
