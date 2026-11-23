import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CmLevelHermitianIntegral
import Formalism.LocalToGlobal.Columns.ToHLatLemmas
import Formalism.LocalToGlobal.Columns.RowFormsGood
import Formalism.LocalToGlobal.Divisibility.ClassSumBridge
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Formalism.QuotientMetricDivisors.ReductionLemmaZero
import Formalism.QuotientMetricDivisors.FinalW
import Formalism.LocalToGlobal.Divisibility.FramesLemmas
import Formalism.LocalToGlobal.GlobalTheory.HLatOpsP
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SlopeStep
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DivisionValues Formalism.L2.DIV Formalism.L2.Col
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_level_hermitian_integral : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (v0 : InfinitePlace K), IsConjAt v0 → ∀ S : CSD K, S.Good 1 → (∀ i j, S.H i j ∈ cmMax K) → (∀ v : InfinitePlace K, (S.H.map v.embedding).PosDef) → ∀ (G : Type) [Group G] [Fintype G] (r : Representation K G S.Forms), S.ActGood r → S.ActRat r → ∀ (P : Subgroup G) (ψ : P →* Kˣ), (∀ i j, S.lvlH r P ψ i j ∈ cmMax K) ∧ (∀ v : InfinitePlace K, ((S.lvlH r P ψ).map v.embedding).PosDef) ∧ Formalism.HermitianLatticesTheory.dual (hform (S.lvlH r P ψ)) (S.lvlNab r P ψ) ≤ S.lvlNab r P ψ := by
  first | exact @GlobalTheory.lvl_consequence_one | exact GlobalTheory.lvl_consequence_one | (intros; apply GlobalTheory.lvl_consequence_one <;> assumption)
