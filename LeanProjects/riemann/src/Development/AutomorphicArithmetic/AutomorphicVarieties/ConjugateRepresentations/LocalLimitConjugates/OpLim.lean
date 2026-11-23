import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.LiftCv
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CvAlg
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.TestOps
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

theorem UpperTheory.V.Cj.H.opLim :
    UpperTheory.V.Cj.H.OpLim := by
  intro E _ _ _ a ha μ _ _ T P hT hP hlim T' P' hT' hP' φ hφ
  induction hφ using Submodule.span_induction with
  | mem φ h =>
    obtain ⟨ψ, F, hψ, hF⟩ := h
    intro C hC
    have hc : Continuous ψ.1 := ((testOps E a ψ).1 hψ.2).1
    obtain ⟨-, hlin, -, hb⟩ := cvAlg (GA E a) (latticeGL E a) μ ψ.1 hc hψ.1
    obtain ⟨B, hB⟩ := hb C hC
    have h1 : ∀ k, (T' k φ).1 = cv ψ.1 (T k F) := fun k =>
      liftCv E a ha μ (T k) (hT k) (T' k) (hT' k) ψ φ F hψ hF
    have h2 : (P' φ).1 = cv ψ.1 (P F) := liftCv E a ha μ P hP P' hP' ψ φ F hψ hF
    have h3 : Tendsto (fun k => B * ‖P F - T k F‖) atTop (𝓝 0) := by
      have h4 : Tendsto (fun k => P F - T k F) atTop (𝓝 (P F - P F)) := tendsto_const_nhds.sub (hlim F)
      have h5 := h4.norm.const_mul B
      simpa using h5
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [h3.eventually (gt_mem_nhds hε)] with k hk x hx
    rw [h1, h2, dist_eq_norm]
    have h6 := congrFun (hlin (P F) (T k F) 1 (-1)) x
    have h7 : (1 : ℂ) • P F + (-1 : ℂ) • T k F = P F - T k F := by
      rw [one_smul, neg_one_smul, sub_eq_add_neg]
    rw [h7] at h6
    have h8 : cv ψ.1 (P F) x - cv ψ.1 (T k F) x = cv ψ.1 (P F - T k F) x := by
      rw [h6]; simp [sub_eq_add_neg]
    rw [h8]
    exact (hB _ x hx).trans_lt hk
  | zero =>
    intro C _
    simp only [map_zero]
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    exact Eventually.of_forall fun k x _ => by simpa using hε
  | add φ ψ _ _ h1 h2 =>
    intro C hC
    simp only [map_add]
    exact (h1 C hC).add (h2 C hC)
  | smul c φ _ h =>
    intro C hC
    simp only [map_smul]
    exact (uniformContinuous_const_smul c).comp_tendstoUniformlyOn (h C hC)
