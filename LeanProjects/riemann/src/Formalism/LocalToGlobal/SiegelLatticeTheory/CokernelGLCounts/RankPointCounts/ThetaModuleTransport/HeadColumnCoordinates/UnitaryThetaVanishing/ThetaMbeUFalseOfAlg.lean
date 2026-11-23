import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitaryThetaVanishing.CoordUHolds

namespace Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.ThetaMbeU

theorem thetaMbeU_false_of_alg (h2 : AlgAll) {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Formalism.MainNotions.S.Loc.Model F E) (r n : ℕ) : Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUL.ThetaMbeU M r n false :=
  thetaMbeU_false_of coordU_holds h2 M r n

end Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.ThetaMbeU
