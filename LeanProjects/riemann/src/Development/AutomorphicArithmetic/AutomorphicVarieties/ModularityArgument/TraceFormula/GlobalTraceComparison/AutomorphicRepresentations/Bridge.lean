import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.ThetaFixedGlobalOfTraceInputs
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InfCharConjEmbeddingNegOfInvariantPairingStatement

open NumberField GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.Desc

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

theorem map_infOf_true {n : ℕ} (l : Formalism.BasicNotions.DomWeight n) :
    Multiset.map (PositivityTheory.RgBcC.infOf l.w true) Finset.univ.val = infOfWeight l := by
  unfold infOfWeight
  refine Multiset.map_congr rfl fun k _ => ?_
  simp [PositivityTheory.RgBcC.infOf]
  try ring

theorem map_infOf_false {n : ℕ} (l : Formalism.BasicNotions.DomWeight n) :
    Multiset.map (PositivityTheory.RgBcC.infOf l.w false) Finset.univ.val = (infOfWeight l).map Neg.neg := by
  unfold infOfWeight
  rw [Multiset.map_map]
  refine Multiset.map_congr rfl fun k _ => ?_
  simp [PositivityTheory.RgBcC.infOf]
  try ring

theorem aux_statement_11 (hG : ThetaFixedGlobalCharacter) (hθ : ThetaFixOf) : ThetaFixedGlobalWeights := by
  intro E _ _ _ n hn π hreg hd lamE hl K h1 h2 h3 h4 _ _ μC _ _ _ μf _ μ _
  refine hG E n hn π hreg (hθ E n hn π hd) (fun w => (lamE w.embedding).w) (fun w => (lamE w.embedding).anti) (fun w => ⟨?_, ?_⟩)
    K h1 h2 h3 h4 μC μf μ
  · rw [map_infOf_true]
    exact hl _
  · rw [map_infOf_false, ← GlobalTheory.T.infChar_conjEmbedding_neg_of_invariant_pairing E n π π hd w.embedding _ _ (hl _) (hl _)]
    exact hl _

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi
