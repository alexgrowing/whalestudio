import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp

namespace UpperTheory.Gal.Int.Inp

structure Inp : Prop where
  js : GlobalTheory.Published.JacquetShalikaRigidity
  gk : GlobalTheory.Published.GelfandKazhdanDual
  adm : GlobalTheory.Published.IrreducibleAdmissibleGL
  len : GlobalTheory.Published.StandardFunctorsFiniteLength
  exh : GlobalTheory.Published.LanglandsExhaustionGL
  zel : GlobalTheory.Published.ZelevinskyPolynomialRing
  gen : GlobalTheory.Published.GenericUnitaryDualGL
  ac : GlobalTheory.Published.ArthurClozelStrongTC
  hk : GlobalTheory.Published.HeckeLAdicCharacterAbove
  alg : GlobalTheory.Published.AlgebraicCharacterWD
  pst : GlobalTheory.Published.DeRhamPotSemistable

end UpperTheory.Gal.Int.Inp
