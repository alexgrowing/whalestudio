import Mathlib
import Formalism.LocalToGlobal.GlobalTheory.GL1.Statement
import Formalism.LocalToGlobal.GlobalTheory.GL1.CompactFixesLattice.SingleMemLam
import Formalism.LocalToGlobal.GlobalTheory.GL1.CompactFixesLattice.SingleMemOrb
import Formalism.GL3MeanSquares.HookFormulaTorsion.DifferenceStableUnderAction
import Formalism.GL3MeanSquares.HookFormulaTorsion.DifferentIdealConditions
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.CMFieldLemmas
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Formalism.FrobeniusOrbits.RealSubfieldLeCompositum

open IsDedekindDomain TensorProduct NumberField Topology

namespace Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion

namespace Tdis

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem td_adic (v : HeightOneSpectrum (𝓞 F)) : TotallyDisconnectedSpace (v.adicCompletion F) := by
  rw [totallyDisconnectedSpace_iff_connectedComponent_zero]
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨mem_connectedComponent, fun x hx => ?_⟩
  by_contra hne
  have hr : (Valued.v : Valuation (v.adicCompletion F) _).restrict x ≠ 0 :=
    (Valuation.zero_iff _).not.mpr hne
  have hc := Valued.isClopen_ball (R := v.adicCompletion F)
    ((Valued.v : Valuation (v.adicCompletion F) _).restrict x)
  have h0 : (0 : v.adicCompletion F) ∈
      {y | (Valued.v : Valuation (v.adicCompletion F) _).restrict y <
        (Valued.v : Valuation (v.adicCompletion F) _).restrict x} := by
    simp only [Set.mem_ofPred_eq, map_zero]
    exact pos_iff_ne_zero.mpr hr
  have h1 := hc.connectedComponent_subset h0 hx
  exact (lt_irrefl ((Valued.v : Valuation (v.adicCompletion F) _).restrict x)) h1

end Tdis

end Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion
