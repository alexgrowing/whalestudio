import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ColMatchAll
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TopPlaceLogTheta
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrdSubConjEqNeg

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Core GlobalTheory.Core.Ht2
attribute [local instance] GlobalTheory.Mem.Col2.starE

noncomputable section

namespace GlobalTheory.Core.Ht2

theorem analyticTies_trueCols : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (h : I.Ok) (hX : B.fields.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l)), ColIn.JetsIn I → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice (I.rec7 l Z) ⊤ I.J.δ ∧ TaylorLogMetric.IsChi (I.rec7 l Z) I.chi ∧ IsDgen (I.rec7 l Z) I.J.cD ∧ ∀ u a, GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds.FieldOfDefinition (Pr := B.primes X) B.wts I.sel (I.tup a) (I.cst a) u I.A := by
  intro B X I h _ l Z hJ
  have hA := (I.J.ok_iff B (I.cols l) Z.W Z.V Z.S Z.N Z.G).1 h.amb_ok
  exact ⟨hA.1, GlobalTheory.Mem.ChiIdeal.isChi_chiId (I.rec7 l Z) I.C.chiPsi I.C.isChi, hA.2, fun u a i hi => hJ a u i hi⟩

end GlobalTheory.Core.Ht2

end
