import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowNormHasGramStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowLatticeFinitelyGeneratedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowGoodLatticeNeBotStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowGoodWeightDictionaryStatement

noncomputable section

open GlobalTheory.CovTop GlobalTheory.BigTop

namespace GlobalTheory.CovTop

theorem gram_of_hypotheses (_h : Hypotheses2) : Gram :=
  ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun _ _ _ _ =>
    ⟨0, le_rfl, 0, fun _ _ _ _ p hp i =>
      ⟨GlobalTheory.T.row_norm_has_gram p hp.1 hp.2 i, GlobalTheory.T.row_lattice_finitely_generated p hp.1 hp.2 i, GlobalTheory.T.row_good_lattice_ne_bot p hp.1 hp.2 i, GlobalTheory.T.row_good_weight_dictionary p hp.1 hp.2 i⟩⟩⟩⟩

end GlobalTheory.CovTop

end
