import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.Descent.CharpolyNilpotence.IsNilpotentAevalCharpoly
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.Descent.NilpotentPowers.IsNilpotentPowSub
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.Descent.SliceVanishing.SliceVanOfFrob
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.Descent.SliceVanishing.Unimodularity.Imports
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.FrobeniusReciprocity.FrobProof

namespace PositivityTheory.RgUd.T.Desc.Final

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Desc

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem sliceVan [CharZero k] : SliceVan (k := k) :=
  SLF.sliceVan_of_frob' PositivityTheory.PfBern.Frob.frobeniusReciprocity SLF.Un2.unimod

theorem descA [CharZero k] : DescA (k := k) := Asm.descA_of JC.jcPoly (sliceVan k)

end PositivityTheory.RgUd.T.Desc.Final
