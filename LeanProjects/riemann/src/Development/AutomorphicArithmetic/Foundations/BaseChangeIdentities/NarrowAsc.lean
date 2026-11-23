import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.Narrow
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.DiscreteSpectrumUnitarity.UsedAsc
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.AscSeedHolds2
import Development.WeilBound.RepresentationTheoryGL.ConstantTermFiniteness.LieInvariants.InvariantOfLieOneLEqZero

open PositivityTheory.Rg.Rs in
theorem UpperTheory.BaseChangeIdentities.ascComp : UpperTheory.BaseChangeIdentities.AscComp := by
  intro E _ _ _ N hN
  refine ⟨fun a π ha hn => ?_, fun V hV a d π hn e =>
    Re.Asc.hasSpehComp ascSeed_holds2.2 PositivityTheory.Rg.HF.GL.automorphicFormsFiniteGL hN hV hn e⟩
  subst ha
  exact ⟨π.V, PositivityTheory.RSHS.L1.cuspDiscrete E _ hN π (GlobalTheory.SpehPair.isUnitary_of_isNormalised hn) hn,
    PDich.ascEmb_one (Setoid.refl π)⟩
