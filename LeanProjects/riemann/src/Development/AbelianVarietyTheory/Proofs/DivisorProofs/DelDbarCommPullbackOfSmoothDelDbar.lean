import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DelOperatorAtDbarOperatorAtLinearLocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DelDbarChainRuleHolomorphicPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasPullbackEqChartExpressionStatement
open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CxForm.HolAtlas

variable {M M' : Type} [TopologicalSpace M] [TopologicalSpace M'] {n n' : ℕ} (A : HolAtlas M n) (A' : HolAtlas M' n')

theorem loc_pullback_eq {f : M' → M} {α : A.Fld} (hf : A.IsHolo A' f) (hα : A.IsForm α) (j : A'.ι) (i : A.ι) :
    IsOpen ((A'.e j).target ∩ (A'.e j).symm ⁻¹' (f ⁻¹' (A.e i).source)) ∧
    ∀ v ∈ (A'.e j).target ∩ (A'.e j).symm ⁻¹' (f ⁻¹' (A.e i).source),
      A'.loc (A.pullback A' f α) j v =
        pull (fderiv ℂ (A.e i ∘ f ∘ (A'.e j).symm) v) (A.loc α i ((A.e i ∘ f ∘ (A'.e j).symm) v)) := by
  refine ⟨(A'.e j).continuousOn_symm.isOpen_inter_preimage (A'.e j).open_target
    ((A.e i).open_source.preimage hf.1), fun v hv => ?_⟩
  have hs : (A'.e j).symm v ∈ (A'.e j).source := (A'.e j).map_target hv.1
  have hτ : (A.e i ∘ f ∘ (A'.e j).symm) v ∈ (A.e i).target := (A.e i).map_source hv.2
  rw [HolAtlas.loc, dif_pos hv.1, HolAtlas.loc, dif_pos hτ,
    GlobalTheory.T.holAtlas_pullback_eq_chart_expression M M' n n' A A' f α hf hα ⟨(j, (A'.e j).symm v), hs⟩ i hv.2]
  have hc : (A'.e j) ((A'.e j).symm v) = v := (A'.e j).right_inv hv.1
  simp only [Pt.crd, Pt.ch, Pt.pt, hc]
  congr 2
  exact Subtype.ext (Prod.ext rfl ((A.e i).left_inv hv.2).symm)

theorem pullback_del_dbar (f : M' → M) (α : A.Fld) (hf : A.IsHolo A' f) (hα : A.IsForm α) :
    A'.del (A.pullback A' f α) = A.pullback A' f (A.del α) ∧
      A'.dbar (A.pullback A' f α) = A.pullback A' f (A.dbar α) := by
  have key : ∀ x : A'.Pt, A'.del (A.pullback A' f α) x = A.pullback A' f (A.del α) x ∧
      A'.dbar (A.pullback A' f α) x = A.pullback A' f (A.dbar α) x := by
    intro x
    have hi : f x.pt ∈ (A.e (A.cover (f x.pt)).choose).source := (A.cover (f x.pt)).choose_spec
    obtain ⟨hU, hloc⟩ := loc_pullback_eq A A' hf hα x.1.1 (A.cover (f x.pt)).choose
    have hx : x.crd ∈ (A'.e x.1.1).target ∩ (A'.e x.1.1).symm ⁻¹' (f ⁻¹' (A.e (A.cover (f x.pt)).choose).source) := by
      refine ⟨(A'.e x.1.1).map_source x.2, ?_⟩
      show (A'.e x.1.1).symm (A'.e x.1.1 x.1.2) ∈ f ⁻¹' (A.e (A.cover (f x.pt)).choose).source
      rw [(A'.e x.1.1).left_inv x.2]
      exact hi
    have hτx : (A.e (A.cover (f x.pt)).choose ∘ f ∘ (A'.e x.1.1).symm) x.crd =
        A.e (A.cover (f x.pt)).choose (f x.pt) := by
      show A.e _ (f ((A'.e x.1.1).symm (A'.e x.1.1 x.1.2))) = _
      rw [(A'.e x.1.1).left_inv x.2]
    have hdiff : ∀ S, DifferentiableAt ℝ (fun y => (bas n).repr (A.loc α (A.cover (f x.pt)).choose y) S)
        ((A.e (A.cover (f x.pt)).choose ∘ f ∘ (A'.e x.1.1).symm) x.crd) := by
      intro S
      rw [hτx]
      exact ((hα.smooth _ S).differentiableOn (by simp)).differentiableAt
        ((A.e _).open_target.mem_nhds ((A.e _).map_source hi))
    have hc := GlobalTheory.T.del_dbar_chainRule_holomorphicPullback n' n _ _ (A.loc α (A.cover (f x.pt)).choose) x.crd hU hx (hf.2 x.1.1 _) hdiff
    have hl := (GlobalTheory.T.delOperatorAt_dbarOperatorAt_linear_local n' x.crd).2.2.2.1 _ _ (Filter.eventually_of_mem (hU.mem_nhds hx) hloc)
    rw [hτx] at hc
    exact ⟨(hl.1.trans hc.1 : _), (hl.2.trans hc.2 : _)⟩
  exact ⟨funext fun x => (key x).1, funext fun x => (key x).2⟩

end GlobalTheory.CxForm.HolAtlas

theorem GlobalTheory.CxForm.HolAtlas.del_dbar_comm_pullback : ∀ (M M' : Type) [TopologicalSpace M] [TopologicalSpace M'] (n n' : ℕ)
    (A : HolAtlas M n) (A' : HolAtlas M' n')
    (f : M' → M) (α : A.Fld), A.IsHolo A' f → A.IsForm α → A.IsForm (A.del α) → A.IsForm (A.dbar α) →
    A'.del (A.pullback A' f α) = A.pullback A' f (A.del α) ∧ A'.dbar (A.pullback A' f α) = A.pullback A' f (A.dbar α) :=
  fun _ _ _ _ _ _ A A' f α hf hα _ _ => HolAtlas.pullback_del_dbar A A' f α hf hα
