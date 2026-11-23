import Formalism.LocalToGlobal.GlobalTheory.HLatOpsP
import Formalism.HarderNarasimhan.FinalCor
import Formalism.QuotientMetricDivisors.ReductionLemmaZero
import Formalism.QuotientMetricDivisors.FinalW
import Formalism.LocalToGlobal.Divisibility.FramesLemmas
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DivisionValues
open scoped Matrix ComplexOrder

namespace GlobalTheory

open Formalism.HN Formalism.LFunctionChainParameters.slopeLatticeData in

theorem muMax_nonpos_of_lcv_nonneg : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (A : HLat K), (∀ v, IsUnit (A.X v).det) → A.L.FG → A.L ≠ ⊥ → (∀ N : Submodule (𝓞 K) A.V, N ≤ A.L → N ≠ ⊥ → 0 ≤ (Formalism.L2.GlobalTheoryTheory.HLatOps.withL A N).lcv) → A.muMax ≤ 0 := by
  intro K _ _ _ _ A hX hL hL0 h
  unfold HLat.muMax
  refine muMaxDef_le A.b A.X hL0 fun Q hQ hQ0 => ?_
  have hQfg : Q.FG := fg_of_le hL hQ
  have hl := h Q hQ hQ0
  simp only [HLat.lcv, Formalism.L2.GlobalTheoryTheory.HLatOps.withL] at hl
  have hd : (0 : ℝ) < (Module.finrank ℚ K : ℝ) := finrank_pos'
  have h2 : (0 : ℝ) < 2 / (Module.finrank ℚ K : ℝ) := by positivity
  have hlog : 0 ≤ Real.log (ht A.b A.X Q) := by
    by_contra hc
    push_neg at hc
    have := mul_neg_of_pos_of_neg h2 hc
    linarith
  rw [muDef_eq_log A.b A.X hX hQfg hQ0]
  haveI : FiniteDimensional K A.V := Module.Finite.of_basis A.b
  have hr : (0 : ℝ) < (rkK Q : ℝ) := by exact_mod_cast rkK_pos hQ0
  apply div_nonpos_of_nonpos_of_nonneg
  · linarith
  · positivity

end GlobalTheory
