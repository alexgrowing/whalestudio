import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HolomorphicDiscreteSeries
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexifiedDerivedActionEqSumKFiniteModuleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KTypeWeightMemConeOverLowestKTypeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKFiniteModuleIrreducibleUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowestKTypeSpaceHolomorphicKModuleKilledStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaisingSpanEqSpanWordsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFiniteSmoothVecOfIrreducibleUnitaryRepStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFiniteSpanRaisingOperatorWordsLowestKTypeStatement

open Matrix GlobalTheory.HolDS

namespace GlobalTheory.HolDS

theorem holomorphicDiscreteSeries_holds : GlobalTheory.Published.HolomorphicDiscreteSeries := by
  intro n ε lam hHC hHol H _ _ σ hDS
  obtain ⟨hc, hnt, hU, hI, -⟩ := id hDS
  haveI := hc
  haveI := hnt
  obtain ⟨D, E, hK⟩ := GlobalTheory.T.exists_kFiniteModule_irreducible_unitary n ε H σ hU hI
  have low := GlobalTheory.T.lowestKTypeSpace_holomorphicKModule_killed n ε H σ D E lam hHC hHol hDS hK
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact fun μ S hS => GlobalTheory.T.kType_weight_mem_cone_over_lowest_kType n ε H σ D E lam hHC hHol hDS hK μ S hS
  · exact fun v hv => GlobalTheory.T.kFinite_smoothVec_of_irreducible_unitaryRep n ε H σ hU hI v hv
  · intro Z hZ v hv
    have hvD : v ∈ D := low.1 hv
    have hx : (⟨v, hvD⟩ : D) ∈ (Formalism.MainNotions.S.lowKSub ε lam σ).comap D.subtype := hv
    have h := GlobalTheory.T.complexifiedDerivedAction_eq_sum_kFiniteModule n ε H σ D E hK Z ⟨v, hvD⟩
    simp only at h
    rw [h]
    have h0 : (∑ a, ∑ b, Z a b • E a b ⟨v, hvD⟩ : D) = 0 := by
      refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
      by_cases hab : ε a = false ∧ ε b = true
      · rw [low.2.2.2 b a hab.2 hab.1 _ hx, smul_zero]
      · rw [hZ a b hab, zero_smul]
    rw [h0]
    rfl
  · intro v
    rw [GlobalTheory.T.raisingSpan_eq_map_span_words_of_isKMod n ε H σ D E hK _ low.1, GlobalTheory.T.kFinite_span_raisingOperator_words_lowestKType n ε H σ D E lam hHC hHol hDS hK,
      Submodule.map_top, Submodule.range_subtype]
    exact (hK.mem v).symm

end GlobalTheory.HolDS
