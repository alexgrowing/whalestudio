import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.JumpsInLetterOfEvenIndex
import Formalism.SharpRestriction.LevelLetterCocycles.At0HomApply
import Formalism.SharpRestriction.LevelLetterCocycles.DlOfQp
import Formalism.SharpRestriction.LevelLetterCocycles.EvaluationAtUniformizerPower

noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.RouteD

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains Formalism.MainNotions.RamifiedCoefficientChains.S9

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n]

theorem dual_lemma_of_wach_hypotheses [IsDomain O] [IsFractionRing O LL] (W : LocWach PD LL O v n)
    (hE : Formalism.MainNotions.RamifiedCoefficientChains.DcrisExactStrict PD LL) (hC : Formalism.MainNotions.RamifiedCoefficientChains.CrysSubQuot PD LL)
    (hQ : Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris PD LL) (h5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (hRu : Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExpRules W) (hEC : Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExpCrit W) (hDT : 11 ≤ PD.p → Formalism.MainNotions.RamifiedCoefficientChains.Sh.DetTool W)
    (hZ : Formalism.MainNotions.RamifiedCoefficientChains.Sh.ZTool W) (hA : Formalism.MainNotions.RamifiedCoefficientChains.S9.ShB.AdaptBas W) : LemmaDN W :=
  Formalism.MainNotions.RamifiedCoefficientChains.S9.DetS.lemmaDN_of_S1E W hZ hA
    (Formalism.MainNotions.RamifiedCoefficientChains.S9.GM.gMem_of W hE hC hQ h5 h9 hRu hEC)
    (Formalism.MainNotions.RamifiedCoefficientChains.S9.DetA.detAlg_of W hE hC hQ h5 h9 (Formalism.MainNotions.RamifiedCoefficientChains.Sh.basTool_of W h9) hDT
      (Formalism.MainNotions.RamifiedCoefficientChains.S9.GCoord.gCoord_holds W))

end Formalism.MainNotions.RamifiedCoefficientChains.S9.RouteD
