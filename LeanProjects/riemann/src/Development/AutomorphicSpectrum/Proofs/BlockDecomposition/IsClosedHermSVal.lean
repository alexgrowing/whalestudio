import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InCell
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousHermPart
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GinfCSecondCountable
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L GlobalTheory.CompanionTheory.MuC
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
namespace GlobalTheory.CompanionTheory.MuC

theorem isClosed_hermS_val (D : D7) (p : ℕ) (e : AE D) :
    IsClosed ((hermS D p e : AddSubgroup (hermA D p)) : Set (hermA D p)) := by
  obtain ⟨_, _, _, _, _⟩ := Formalism.IndefR.Eqv.ae_facts D
  have hc : Continuous fun x : hermA D p => e • (x : Formalism.IndefR.Datum.Mx D p p) :=
    (continuous_const_smul e).comp continuous_subtype_val
  exact isClosed_eq hc continuous_subtype_val

set_option synthInstance.maxHeartbeats 400000 in

theorem hermS_facts : ∀ (D : D7) (p : ℕ) (e : AE D), LocallyCompactSpace (hermS D p e) ∧ T2Space (hermS D p e) ∧
    SecondCountableTopology (hermS D p e) ∧ BorelSpace (hermS D p e) ∧ IsTopologicalAddGroup (hermS D p e) := by
  intro D p e
  obtain ⟨_, _, _, _, _⟩ := Formalism.IndefR.Eqv.ae_facts D
  have hS := isClosed_hermS_val D p e
  have hA : IsClosed ((hermA D p : AddSubgroup (Formalism.IndefR.Datum.Mx D p p)) : Set (Formalism.IndefR.Datum.Mx D p p)) :=
    GlobalTheory.CompanionTheory.HermVol.isClosed_hermA
  haveI : LocallyCompactSpace (Formalism.IndefR.Datum.Mx D p p) :=
    show LocallyCompactSpace (Fin p → Fin p → AE D) from inferInstance
  haveI : SecondCountableTopology (Formalism.IndefR.Datum.Mx D p p) :=
    show SecondCountableTopology (Fin p → Fin p → AE D) from inferInstance
  haveI : BorelSpace (Formalism.IndefR.Datum.Mx D p p) := by
    first
    | exact show BorelSpace (Fin p → Fin p → AE D) from inferInstance
    | exact ⟨rfl⟩
    | exact Matrix.borelSpace
  haveI : SecondCountableTopology (hermA D p) := by
    first
    | exact Topology.IsInducing.subtypeVal.secondCountableTopology
    | exact Topology.IsEmbedding.subtypeVal.secondCountableTopology
    | exact show SecondCountableTopology ((hermA D p : Set (Formalism.IndefR.Datum.Mx D p p))) from inferInstance
  haveI : SecondCountableTopology (hermS D p e) := by
    first
    | exact Topology.IsInducing.subtypeVal.secondCountableTopology
    | exact Topology.IsEmbedding.subtypeVal.secondCountableTopology
    | exact show SecondCountableTopology ((hermS D p e : Set (hermA D p))) from inferInstance
  haveI : LocallyCompactSpace (hermA D p) := hA.isClosedEmbedding_subtypeVal.locallyCompactSpace
  exact ⟨hS.isClosedEmbedding_subtypeVal.locallyCompactSpace, inferInstance, inferInstance, inferInstance,
    inferInstance⟩

end GlobalTheory.CompanionTheory.MuC
