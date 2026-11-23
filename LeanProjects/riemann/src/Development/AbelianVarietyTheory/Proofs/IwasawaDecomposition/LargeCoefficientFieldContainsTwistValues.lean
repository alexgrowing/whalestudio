import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
import Formalism.LocalToGlobal.Columns.PathCountSymmetricHolds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAlgebraicRootsCoeffFieldContainsTwistValueStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowsLiftsHeckeOperatorsCommuteStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoefficientFieldContainsHeckeEigenvaluesStatement

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.R3.OkVals

theorem isConjAt_embLL (B : Base) : Formalism.DivisionValues.IsConjAt (InfinitePlace.mk B.embLL) := fun a => by
  rcases InfinitePlace.embedding_mk_eq B.embLL with e | e
  · rw [e]
    exact B.starLL_cx a
  · rw [e, ComplexEmbedding.conjugate_coe_eq, ComplexEmbedding.conjugate_coe_eq, B.starLL_cx a]

theorem ev_of_forall {p : Top.Ctx → Prop} (h : ∀ K, p K) : Top.Ev p :=
  ⟨1 / 100, by norm_num, fun _ _ _ _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun _ _ _ _ =>
    ⟨0, fun _ _ => ⟨0, fun _ _ => ⟨0, fun K _ _ _ _ _ => h K⟩⟩⟩⟩⟩

theorem large_coefficientField_contains_twist_values : Top.EvLg fun _ B f T => ∀ (px : PreX B.toPre) (I : Col2.ColIn B px) (hX : B.fields.Ok), I.Ok → I.C = f →
    Set.range I.xi = T.set f → ValsIn I ∧ ∀ U Xg tr, (∀ χ ∈ Xg, IsAbsIrrChar χ) → (famC I hX U Xg tr).fam3.Ok3 1 := by
  obtain ⟨Sv, hSv, hV⟩ := GlobalTheory.T.exists_algebraicRoots_coeffFieldContainsTwistValues
  obtain ⟨So, hSo, hF⟩ := GlobalTheory.T.exists_coefficientField_contains_heckeEigenvalues
  unfold Top.EvLg
  refine ev_of_forall fun _ => ?_
  unfold Top.large₂
  refine ⟨fun _ _ _ => ∅, fun _ _ _ _ => ∅, fun _ _ _ _ _ => ∅,
    fun P f F F₀ Ξ => Sv P Ξ ∪ So P f F F₀ Ξ, fun _ _ _ z hz => absurd hz (Finset.notMem_empty z), ?_, ?_⟩
  · intro P f F F₀ Ξ z hz
    rcases Finset.mem_union.1 hz with h | h
    · exact hSv P Ξ z h
    · exact hSo P f F F₀ Ξ z h
  intro B f T _ hH _ _ px I hX hOk hC hR
  have hL : ∀ z ∈ Sv B.toPre (Set.range I.xi) ∪ So B.toPre I.C B.KsC B.fixedCoefficientFieldInComplex (Set.range I.xi), z ∈ B.LLC := by
    rw [hR, hC]
    exact hH.2
  refine ⟨hV B px I hOk fun z hz => hL z (Finset.mem_union_left _ hz), fun U Xg tr hirr => ?_⟩
  have hFI := hF B px I hX hOk fun z hz => hL z (Finset.mem_union_right _ hz)
  have hC2 := GlobalTheory.T.rowsLifts_heckeOperators_commute B px I hX hOk
  have key : ∀ τ : TupU I U, ∃ a : I.ι, I.tup a = τ.1 := fun τ => ⟨_, tup_ixOf I τ⟩

  have hH3 : ColHyp3 B.wts I.Ch I.sel (InfinitePlace.mk B.embLL) (tuOf I U) Xg ∅ := by
    refine ⟨⟨isConjAt_embLL B, hirr, fun τ => Formalism.L2.Col.heckeOperators_commute _ _, fun τ => ?_,
      fun j τ => Formalism.L2.Col.heckeOperators_commute _ _, fun j τ => ?_⟩, fun τ => ?_, fun τ => ?_, fun j τ => ?_, fun j τ => ?_⟩
    · obtain ⟨a, ha⟩ := key τ
      rw [← ha]
      exact fun i => (hFI a).1 (Sum.inl i)
    · obtain ⟨a, ha⟩ := key τ
      rw [← ha]
      exact fun i => (hFI a).2 j (Sum.inl i)
    · obtain ⟨a, ha⟩ := key τ
      rw [← ha]
      exact (hC2 a).1
    · obtain ⟨a, ha⟩ := key τ
      rw [← ha]
      exact fun i => (hFI a).1 (Sum.inr i)
    · obtain ⟨a, ha⟩ := key τ
      rw [← ha]
      exact (hC2 a).2 j
    · obtain ⟨a, ha⟩ := key τ
      rw [← ha]
      exact fun i => (hFI a).2 j (Sum.inr i)
  have h := colFam3_ok B.wts I.Ch I.sel hX (InfinitePlace.mk B.embLL) (tuOf I U) Xg ∅ (xiValOf I) tr hH3
  exact h

end GlobalTheory.Mem.R3.OkVals

end
