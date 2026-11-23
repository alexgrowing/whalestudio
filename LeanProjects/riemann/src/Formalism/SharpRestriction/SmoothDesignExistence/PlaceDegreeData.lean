import Formalism.SharpRestriction.CuspSpanNormBounds.PlaceDegreeData
import Formalism.SharpRestriction.SmoothDesignExistence.DGamSmooth

noncomputable section

namespace Formalism.MainNotions.Pk

open Formalism.BasicNotions

structure CountingHypotheses : Prop where

  p30 : PlaceDegreeData.UniformExportStatement
  admOne : ∀ D : D7, PlaceDegreeData.adm1 D
  local_admissible_second : ∀ D : D7, PlaceDegreeData.adm2 D
  local_admissible_third : ∀ D : D7, PlaceDegreeData.adm3 D
  siegelMassRatioAlt : Formalism.HermitianLatticesTheory.SiegelMassRatio
  admFive : ∀ D : D7, PlaceDegreeData.adm5 D
  local_admissible_sixth : ∀ D : D7, PlaceDegreeData.adm6 D
  residueConstantBound : ∃ Cres : ℝ, ∀ D : D7, PlaceDegreeData.adm7 D Cres
  admEight : ∀ D : D7, PlaceDegreeData.adm8 D

end Formalism.MainNotions.Pk

end
