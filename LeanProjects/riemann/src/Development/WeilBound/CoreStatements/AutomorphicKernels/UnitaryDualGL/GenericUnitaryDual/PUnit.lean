import Mathlib
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.GenericIrreducibility.GenUnitCCOf
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CentredSegments.Development
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinZelevinskyGL.TopStd
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.ConjDual
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.SegmentJacquetSubquotients.SegmentRepresentation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SquareIntegrableUnitarizableStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentJacquetAllStatement

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

namespace PositivityTheory.Gud.Pf

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem unitarisable_of_unitCC [CharZero k] {Δ : Segment k} {δ : IrrGL k} (hL : IsLSeg Δ δ.rep)
    (hU : PositivityTheory.RgUd.UOrder.UnitCC δ.rep) : IsUnitarisable δ.rep := by
  have hA : GlobalTheory.Published.IrreducibleAdmissibleGL := PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top
  have sq := Zls.FreeSingleHomotopyEquivDiscreteChains.centredSegSqInt k hA PositivityTheory.Tls2.BZGL.standardFunctorsFiniteLength_top
    (GlobalTheory.CompanionTheory.SegCoarse.lSegJacquet hA PositivityTheory.RgGu.segmentRepresentation)
  haveI : Nontrivial δ.snd.rep.V := GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible δ.snd.rep.irr
  have hsq : IsSqIntCoeff δ.rep := sq Δ δ hL (fun t c hc => PositivityTheory.RgUd.UOrder.norm_eq_one_of_unitCC hU hc)
  exact GlobalTheory.SqIntUnit.main k _ _ δ.rep δ.snd.rep.smooth δ.snd.rep.irr hsq

end PositivityTheory.Gud.Pf

end
