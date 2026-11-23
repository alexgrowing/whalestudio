import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonnePerfd
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChainStatementOfPrismaticStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdmissibleModelCommutesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConsStatementOfPrismaticStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalAtOfLocalRootsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalStatementOfChainStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TermStatementOfAlterationStatement

set_option autoImplicit false

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4O

namespace GlobalTheory.DeRhamHodgeTateGoodPrimes

theorem onObj_aux3At_of_knownResults : HypothesesXH → Hypotheses2 → HypothesesH → GlobalTheory.Published.PrismaticDieudonnePerfd →
    OnObj fun _ O _ _ _ _ => DeRhamMinusHodgeTateGoodPrimesAt O.Y := by
  intro hX h₁ h₂ h₃ D O hO _ _ _ _ _
  refine (GlobalTheory.MixedLocalChains.globalHeightBound_iff_atGoodPrimes O.Y).2 fun p hp h2 hu hl => ?_
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨ι, _, w, W, hW, jc, z, hpin, hT⟩ := GlobalTheory.T.term_statement_of_alteration hX.y.alt h₁ h₂ D O hO p h2 hu hl
  refine GlobalTheory.T.global_at_of_local_roots D O.Y p ι w jc _ _ hu hT fun la => ⟨?_, ?_, ?_, ?_⟩
  · exact fun t τ ht => ⟨GlobalTheory.ShFam.Pad.rootOf_lie (z la) ht, GlobalTheory.ShFam.Pad.rootOf_om (z la) ht⟩
  · exact GlobalTheory.T.admissible_model_commutes D _ _ _ O.S O.κ p Fact.out (W la) (hW la) (z la) (jc la)
  · exact GlobalTheory.T.cons_statement_of_prismatic h₁ h₂ D O hO p h2 hu hl (W la) (hW la) (jc la) (hpin la) (z la)
  · exact GlobalTheory.T.local_statement_of_chain (GlobalTheory.T.chain_statement_of_prismatic hX h₁ h₂ h₃) D O hO p h2 hu hl (W la) (hW la) (jc la) (hpin la) (z la)

end GlobalTheory.DeRhamHodgeTateGoodPrimes
