import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.BlochKatoGeneratorBound
import Development.AbelianVarietyTheory.Counterexamples.NonGaloisSurvey.CrystallineCyclotomic
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete

noncomputable section

namespace GlobalTheory.Survey.H1fGeneratorsBis

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.GaloisLatticeModuleActions GlobalTheory.Survey.CrystallineCyclotomic

section

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL]

variable {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]

end

def H1fGeneratorsStandard : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), GlobalTheory.Per.IsStd P AI →
    H1fGeneratorBoundAt P

end GlobalTheory.Survey.H1fGeneratorsBis
