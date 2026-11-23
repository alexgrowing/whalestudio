import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PlaceCharacterEqReferenceIff
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.Mem.R3.GoodProj

theorem rowForm_rE {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {s : ℕ}
    (ok : A.fam.Ok s) (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (t : T) (x : Fin (rDim D A P ψ t) → D.what₂.LL) :
    rowForm A P ψ t ((rE D A P ψ t).mulVec x) =
      (A.MtildeCSD t).gaOp (A.leftGroupActionRight t) (idemOf A.X) (rowForm A P ψ t x) := by
  have hc := (idempotent_spec _ A.v0 ok.conj G A.X ok.irr).2
  have h1 := (level_operator_spec _ A.v0 ok.conj (A.fam.R t).S ((ok.what₂ t).hpos A.v0) G (A.fam.R t).r (ok.what₂ t).act
    (A.fam.lvl P ψ).P (A.fam.lvl P ψ).ψ (idemOf A.X) (hc _).symm).1
  unfold rowForm rE
  change _ = (A.fam.R t).S.gaOp (A.fam.R t).r (idemOf A.X) _
  rw [Matrix.mulVec_mulVec, h1, ← Matrix.mulVec_mulVec, CSD.gaMat, Matrix.sum_mulVec, map_sum]
  rw [CSD.gaOp]
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Matrix.smul_mulVec, map_smul]
  exact congrArg _ (Subtype.ext (action_matrix_spec _ (A.fam.R t).S G (A.fam.R t).r g _))

end GlobalTheory.Mem.R3.GoodProj
