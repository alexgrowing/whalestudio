import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.HermitianCellMeasures.EmDefs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsClosedHermSVal

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.RswEmTop

set_option synthInstance.maxHeartbeats 400000 in

theorem topX : PositivityTheory.Rg.Rsw.Em.TopX := by
  intro D a r t e
  obtain ⟨h1, h2, h3, h4, -⟩ := Formalism.IndefR.Eqv.ae_facts D
  haveI : IsTopologicalRing (AE D) := h1
  haveI : T2Space (AE D) := h2
  haveI : LocallyCompactSpace (AE D) := h3
  haveI : SecondCountableTopology (AE D) := h4
  obtain ⟨s1, -, s3, s4, -⟩ := GlobalTheory.CompanionTheory.MuC.hermS_facts D t e
  haveI b1 : BorelSpace (Mx D a r) := ⟨rfl⟩
  haveI b2 : BorelSpace (Mx D a t) := ⟨rfl⟩
  haveI : LocallyCompactSpace (Mx D a r) := inferInstanceAs (LocallyCompactSpace (Fin a → Fin r → AE D))
  haveI : LocallyCompactSpace (Mx D a t) := inferInstanceAs (LocallyCompactSpace (Fin a → Fin t → AE D))
  haveI : T2Space (Mx D a r) := inferInstanceAs (T2Space (Fin a → Fin r → AE D))
  haveI : T2Space (Mx D a t) := inferInstanceAs (T2Space (Fin a → Fin t → AE D))
  haveI : SecondCountableTopology (Mx D a r) :=
    inferInstanceAs (SecondCountableTopology (Fin a → Fin r → AE D))
  haveI : SecondCountableTopology (Mx D a t) :=
    inferInstanceAs (SecondCountableTopology (Fin a → Fin t → AE D))
  haveI bP : BorelSpace (Mx D a r × Mx D a t) := Prod.borelSpace
  have c1 : Continuous fun z : Mx D a r × Mx D a t => e • z.1 := continuous_fst.const_smul e
  have c2 : Continuous fun z : Mx D a r × Mx D a t => e • z.2 := continuous_snd.const_smul e
  have hC : IsClosed {z : Mx D a r × Mx D a t | e • z.1 = z.1 ∧ e • z.2 = z.2} :=
    (isClosed_eq c1 continuous_fst).inter (isClosed_eq c2 continuous_snd)
  have hE := hC.isClosedEmbedding_subtypeVal
  exact ⟨inferInstance, hE.locallyCompactSpace, TopologicalSpace.Subtype.secondCountableTopology _,
    Subtype.borelSpace _, bP, MeasurableEmbedding.subtype_coe hC.measurableSet, s4, s3, s1⟩

end GlobalTheory.CompanionTheory.RswEmTop
