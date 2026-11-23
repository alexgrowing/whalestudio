import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.LeviActionCommutesWithBoundary
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.FarRegularity.LKTExists
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.DifferentialBoundedSupport
open Finset CompanionTheory.RgExh CompanionTheory.RgExh.U
open CompanionTheory.D.LK (Pos Cn ann cre lift bd om cpt allT LocFin)
open Formalism.REAL (GlRel KHighest IsWeight)
open CompanionTheory.D.DSIC (KUnit)
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_action_commutes_with_boundary : ∀ (n : ℕ) (lev : Fin n → ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V),
    Monotone lev → GlRel E → ∀ p q : Fin n, lev p = lev q → ∀ x : Cn n V, SuppIn (inU lev) x →
      lF E p q (bd (allT n) E x) = bd (allT n) E (lF E p q x) := by
  first | exact @GlobalTheory.CompanionTheory.LeviChain.lF_bd_comm | exact GlobalTheory.CompanionTheory.LeviChain.lF_bd_comm | (intros; apply GlobalTheory.CompanionTheory.LeviChain.lF_bd_comm <;> assumption)
