import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.OrderedCreationCommutesPastLevi
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.FarRegularity.LKTExists
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.DifferentialBoundedSupport
open Finset CompanionTheory.RgExh CompanionTheory.RgExh.U
open CompanionTheory.D.LK (Pos Cn ann cre lift bd om cpt allT LocFin)
open Formalism.REAL (GlRel KHighest IsWeight)
open CompanionTheory.D.DSIC (KUnit)
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ordered_creation_commutes_past_levi : ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V),
    (∀ e : Pos n, (bd (allT n) E * cre e + cre e * bd (allT n) E : Module.End ℂ (Cn n V)) = lF E e.1.1 e.1.2) →
    ∀ (l : List (Pos n)) (x : Cn n V),
      (∀ (pre : List (Pos n)) (f : Pos n) (post : List (Pos n)), l = pre ++ f :: post → ∀ e ∈ l, ∀ k : Pos n,
        adC e.1.1 e.1.2 f k ≠ 0 → k ∈ post) →
      (∀ e ∈ l, lF E e.1.1 e.1.2 x = 0) →
      bd (allT n) E (((l.map cre).prod : Module.End ℂ (Cn n V)) x) =
        (-1 : ℂ) ^ l.length • ((l.map cre).prod : Module.End ℂ (Cn n V)) (bd (allT n) E x) := by
  first | exact @GlobalTheory.CompanionTheory.FarReg.BdProd.bd_prod | exact GlobalTheory.CompanionTheory.FarReg.BdProd.bd_prod | (intros; apply GlobalTheory.CompanionTheory.FarReg.BdProd.bd_prod <;> assumption)
