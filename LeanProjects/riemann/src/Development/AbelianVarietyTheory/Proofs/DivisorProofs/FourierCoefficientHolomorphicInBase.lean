import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChSingle
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FderivIntegralApplyOfHolomorphicOfDominated
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.FamilyFourier
open scoped Real ContDiff

namespace GlobalTheory

open Complex in

theorem differentiableOn_coef_of_holomorphic :
    ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
      {U : Set E} (h : Pt E g → ℂ), IsOpen U → DifferentiableOn ℂ h (cov U g) →
      ∀ n : Fin g → ℤ, DifferentiableOn ℂ (coef h n) U := by
  intro g E _ _ _ U h hU hh n
  have hopen : IsOpen (cov U g) := hU.prod isOpen_univ
  have hcx : Continuous (fun x : Fin g → ℝ => fun i => (x i : ℂ)) := by fun_prop
  have key := differentiableOn_setIntegral_of_holomorphic_of_continuousOn (μ := volume)
    (V := ℂ)
    (F := fun (x : Fin g → ℝ) (b : E) => h (b, fun i => (x i : ℂ)) *
      cexp (-(2 * π * I) * ∑ i, (n i : ℂ) * (x i : ℂ)))
    hU (S := Set.Icc (0 : Fin g → ℝ) 1) (K := Set.Icc (0 : Fin g → ℝ) 1) isCompact_Icc
    subset_rfl measurableSet_Icc isCompact_Icc.measure_lt_top.ne ?_ ?_
  · exact key.1
  · have h1 : ContinuousOn (fun p : (Fin g → ℝ) × E => h (p.2, fun i => (p.1 i : ℂ)))
        (Set.Icc (0 : Fin g → ℝ) 1 ×ˢ U) := by
      refine hh.continuousOn.comp (f := fun p : (Fin g → ℝ) × E => (p.2, fun i => (p.1 i : ℂ)))
        (by fun_prop) ?_
      intro p hp
      exact ⟨hp.2, Set.mem_univ _⟩
    have h2 : Continuous (fun p : (Fin g → ℝ) × E =>
        cexp (-(2 * π * I) * ∑ i, (n i : ℂ) * (p.1 i : ℂ))) := by fun_prop
    exact h1.mul h2.continuousOn
  · intro x _
    have hm : DifferentiableOn ℂ (fun b : E => (b, fun i => (x i : ℂ))) U :=
      (differentiable_id.prodMk (differentiable_const _)).differentiableOn
    exact (hh.comp hm (fun b hb => ⟨hb, Set.mem_univ _⟩)).mul_const _

end GlobalTheory
