import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.KugaSm
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.DelLev
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.SqOrth
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.LevLin
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

theorem UpperTheory.V.Cj.H.resExact :
    UpperTheory.V.Cj.H.ResExact := by
  intro E _ _ _ a ha n e he U Ξ r c hc q ω hω hd
  obtain ⟨k0, k1⟩ := kugaSm E a n e he Ξ r c hc
  cases q with
  | zero => exact ⟨k0 ω hω.equiv hd, fun _ _ => trivial⟩
  | succ q =>
    have hk := k1 q ω hω.equiv hd
    obtain ⟨d1, d2⟩ := delLev E a n e he U Ξ r q ω
    obtain ⟨l1, l2, -⟩ := levLin E a U Ξ q
    have hl := d1 hω
    refine ⟨⟨(-1 : ℂ) • del (smAdj Ξ r) e ω + (0 : ℂ) • del (smAdj Ξ r) e ω, l1 _ _ _ _ hl hl, ?_⟩, fun hs h0 => ?_⟩
    · rw [l2, hk, zero_smul, add_zero]
      exact AlternatingMap.ext fun X => neg_one_smul ℂ _
    · rw [hk, neg_eq_zero] at h0
      exact (sqOrth E a ha n e he Ξ r q).2 ω hs (d2 hs) h0
