import Development.DiscreteGroups.GlobalIrreducibility.DzMatchCut
import Development.DiscreteGroups.GlobalIrreducibility.DzLCusp
import Development.DiscreteGroups.GlobalIrreducibility.DzLDepth
import Development.DiscreteGroups.GlobalIrreducibility.DzLTame
import Development.DiscreteGroups.GlobalIrreducibility.EqTraceSmulOfFinrankOne
import Development.DiscreteGroups.GlobalIrreducibility.DzPinFinal
import Development.DiscreteGroups.GlobalIrreducibility.DzDigMain
import Development.DiscreteGroups.GlobalIrreducibility.DzKondo
import Development.DiscreteGroups.GlobalIrreducibility.DzFinPair
import Development.DiscreteGroups.GlobalIrreducibility.ExistsEqMulShiftToCircle
import Development.DiscreteGroups.GlobalIrreducibility.FixedNeBotOfEquiv
import Development.DiscreteGroups.GlobalIrreducibility.PhiTilde
import Development.DiscreteGroups.GlobalIrreducibility.LTw
import Development.DiscreteGroups.GlobalIrreducibility.DzTameRec
import Development.DiscreteGroups.GlobalIrreducibility.LConvGen
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChevalleyUnitsStatement
import Development.DiscreteGroups.GlobalIrreducibility.DzFeMain
import Development.DiscreteGroups.GlobalIrreducibility.DzFeIter
import Development.DiscreteGroups.GlobalIrreducibility.DzGalEps

namespace DiscreteGroups.sglob.DzType

theorem lFE : LFE := DiscreteGroups.sglob.DzFe.lFE_of_fe DiscreteGroups.sglob.DzFe.fe

theorem artEx_of (hX : GlobalTheory.Published.LocalLanglandsExists) : ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] (A : ValuationSubring Ω) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (h : Formalism.ConjugateSelfDual.IsPlaceOver A v), ∃ a, GlobalTheory.LocLanglands.IsLocalArtin h a := by
  intro L Ω _ _ _ _ _ A v h
  obtain ⟨rc, a, ha, -⟩ := hX L Ω A v h
  exact ⟨a, ha⟩

theorem narrowBig_holds (art : GlobalTheory.Published.GlobalArtinReciprocity) (chev : GlobalTheory.Published.ChevalleyUnits)
    (hX : GlobalTheory.Published.LocalLanglandsExists) (bern : GlobalTheory.Published.BernsteinUnitaryProductIrreducible) : NarrowBig :=
  narrowBig_of lCusp lDepth lTame
    (lMatchBig_of lCusp lDepth (lOneOf (lTameRec art chev)) (lPin_of_dig dig) lKondo (lFinPair lFE) lPsi (lGen bern)
      (lRed DiscreteGroups.sglob.LConv.cuspGen) lTw (galEps_of_art (artEx_of hX) (lTameRec art chev)))

end DiscreteGroups.sglob.DzType
