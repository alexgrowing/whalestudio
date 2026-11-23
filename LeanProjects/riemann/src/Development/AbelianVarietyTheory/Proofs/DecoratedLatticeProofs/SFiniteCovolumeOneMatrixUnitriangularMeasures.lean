import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.Unf

theorem sFinite_vol : ∀ (D : D7) (ρ m : ℕ) (vb : VolM D ρ m) (vU : VolU D ρ), SFinite vb.μ ∧ SFinite vU.ν := by
  intro D ρ m vb vU
  constructor
  · obtain ⟨i1, i2, i3, -⟩ := lattice_Mx D ρ m
    haveI : IsTopologicalAddGroup (Mx D ρ m) := i1
    haveI : LocallyCompactSpace (Mx D ρ m) := i2
    haveI : SecondCountableTopology (Mx D ρ m) := i3
    haveI : vb.μ.IsAddHaarMeasure := vb.covol.1
    haveI : SigmaFinite vb.μ := Measure.IsAddHaarMeasure.sigmaFinite _
    infer_instance
  · obtain ⟨i1, i2, -⟩ := GlobalTheory.UnitU.topology D ρ
    haveI : LocallyCompactSpace (UX D ρ) := i1
    haveI : SecondCountableTopology (UX D ρ) := i2
    haveI : vU.ν.IsHaarMeasure := vU.unit.1
    haveI : SigmaFinite vU.ν := Measure.IsHaarMeasure.sigmaFinite _
    infer_instance

end GlobalTheory.Unf
