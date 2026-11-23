import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.UnitaryHypotheses.NabsDetScalar
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.UnitaryDensity.UDens
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.PositiveShells.PsdLeftZero
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.SubquotientEigenvectors.ExistsEigenOfSubquot
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.IsotropicAtoms.EventuallyMemLat
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.LatticeIndexLifts.ULift

namespace PositivityTheory.RgUd.Form.U.Final

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem derivTop : PositivityTheory.RgUd.ThmB k → PositivityTheory.RgUd.DerivTop k := fun hB =>
  (Asm.uAsm (k := k) (Atom.uAtom (k := k)) (Dens.uDens k) (Atom.uSplit (k := k)) (Lift2.uLift (k := k)) (Shell.uShell (k := k)) (Eig.uEig k) (Eig.uAdm k) hB).1

theorem derivPos : PositivityTheory.RgUd.ThmB k → PositivityTheory.RgUd.DerivPos k := fun hB =>
  (Asm.uAsm (k := k) (Atom.uAtom (k := k)) (Dens.uDens k) (Atom.uSplit (k := k)) (Lift2.uLift (k := k)) (Shell.uShell (k := k)) (Eig.uEig k) (Eig.uAdm k) hB).2

end PositivityTheory.RgUd.Form.U.Final
