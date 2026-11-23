import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramBoundStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramBoundStatementStatement

section
noncomputable section
open GlobalTheory.CovTop GlobalTheory.BigTop
namespace GlobalTheory.CovTop
theorem covering_gram_matrix_of_local_traces (_h : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) : Gram :=
  ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun _ _ _ _ =>
    ⟨0, le_rfl, 0, fun _ _ _ _ p hp i =>
      ⟨GlobalTheory.T.row_norm_has_gram p hp.1 hp.2 i, GlobalTheory.T.row_lattice_finitely_generated p hp.1 hp.2 i, GlobalTheory.T.row_good_lattice_ne_bot p hp.1 hp.2 i, GlobalTheory.T.row_good_weight_dictionary p hp.1 hp.2 i⟩⟩⟩⟩
end GlobalTheory.CovTop
end
end

section
open GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.covering_gram_matrix_criterion : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → Gram := by
  first | exact @_root_.GlobalTheory.CovTop.covering_gram_matrix_of_local_traces | exact _root_.GlobalTheory.CovTop.covering_gram_matrix_of_local_traces | (intros; apply _root_.GlobalTheory.CovTop.covering_gram_matrix_of_local_traces <;> assumption)
end
