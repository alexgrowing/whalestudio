import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ResidualIrreducibilityFormsEquivalent
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.AutomorphicGaloisAdmissible

noncomputable section

namespace UpperTheory.GalC

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain

def CutRec (D : D7) : Prop :=
  ∀ i : D.nd.Loc, ∀ P : D.naut.AV i, D.naut.ptV i P ≠ none →
    ∀ (k : Fin 2), ∀ w ∈ placesOver D.host.E (D.host.g k), UpperTheory.GalS.Nc D.nd D.naut (D.naut.locV i P w)

structure Pre (D : D7) (C : NChoice D) : Prop where
  what₂ : GlobalTheory.NRows.Rows D
  adm : SumRepresentations.admitted D
  Conclusion1 : SumRepresentations.Conclusion1 D
  z : SumRepresentations.ConclusionZ D
  rhoBar : ResidualIrreducibleRankR D
  g3p : AdmissibleThreePrime.LabelDegreeHypotheses D
  weight : GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.WeightParam D
  block : GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.BlockCharParam D
  muUnr : GlobalTheory.HubX.MuUnr D
  depthG : GlobalTheory.HubX.DepthZeroG D
  bc : SphericalInertData.Conclusion1 D
  lam : GlobalTheory.NRows.LamUsed D
  c2 : KillingConditions.LocalisationUniqueness D
  large : GlobalTheory.CoefDuty.Large D
  nct : NChTie D C
  trip : GlobalTheory.PtCore.TriplesGood D
  same : GlobalTheory.PtCore.SameTwist D C
  good : GoodFTAll D

def Tie4 (D : D7) : Prop :=
  PairedCharacterCondition.tieChi (D := D) ∧ (∃ Q : PairedCharacterCondition.Pend D, PairedCharacterCondition.admDZ Q ∧ GlobalTheory.Pass.EigSpan Q) ∧ GlobalTheory.Pass.TieInePoly D ∧ GlobalTheory.TypeLeaf.SerLoc D

structure CutD (D : D7) where
  keep : D.nd.Loc → Prop
  Xs : ∀ i, Set (D.nd.X i)
  ne : ∀ i, keep i → (Xs i).Nonempty

def CutD.all (D : D7) : CutD D := ⟨fun _ => True, fun _ => Set.univ, fun _ _ => Set.univ_nonempty⟩

structure CutD.Good {D : D7} (c : CutD D) : Prop where
  keep : ∀ i, c.keep i ↔ (D.nd.Zgood i).Nonempty
  good : ∀ i, ∀ x ∈ D.nd.Zgood i, x ∈ c.Xs i
  theta : ∀ i, ∀ x ∈ D.nd.Z i, x ∈ c.Xs i → x ∈ D.nd.Zgood i
  op : ∀ i, c.keep i → ∃ α : Module.End (D.nd.O i) (D.nd.Mt i),
    (∀ f : D.nd.T i, α * D.nd.act i f = D.nd.act i f * α) ∧
    (∀ x ∈ D.nd.Zgood i, ∀ u ∈ heckeEig (D.nd.T i) (D.nd.act i) x,
      α.baseChange (FractionRing (D.nd.O i)) u = ((D.what₂.restRowsFiniteGroupCard : ℤ) : FractionRing (D.nd.O i)) • u) ∧
    ∀ x, x ∉ c.Xs i → ∀ u ∈ heckeEig (D.nd.T i) (D.nd.act i) x, α.baseChange (FractionRing (D.nd.O i)) u = 0
  nice : ∀ i, c.keep i → ∀ P : D.naut.AV i, ∀ x ∈ c.Xs i, D.naut.ptV i P = some x →
    ∀ (k : Fin 2), ∀ w ∈ placesOver D.host.E (D.host.g k), UpperTheory.GalS.Nc D.nd D.naut (D.naut.locV i P w)

end UpperTheory.GalC
