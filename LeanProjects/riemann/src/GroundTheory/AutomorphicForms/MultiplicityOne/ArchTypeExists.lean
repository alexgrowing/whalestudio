import Mathlib
import GroundTheory.AutomorphicForms.MultiplicityOne.FinitePart
import GroundTheory.AutomorphicForms.WhittakerCriterion
import GroundTheory.AutomorphicForms.MultiplicityOne.NormOne

open MeasureTheory Set Filter Topology Function
open NumberField IsDedekindDomain

namespace GroundTheory.Automorphic

noncomputable section

namespace MultiplicityOne

open Reduction AutomorphicForm CuspidalSpectrum FourierWhittaker

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {σ : UnitaryRep (normOneGL K n) H}
variable {μ : Measure (normOneGL K n)} [μ.IsHaarMeasure]

theorem map_integrated_of_left_invariant {f : CompactlySupportedContinuousMap (normOneGL K n) ℂ}
    {h : normOneGL K n} (hf : ∀ x, f (h⁻¹ * x) = f x) (v : H) :
    σ h (σ.integrated μ (UnitaryRep.ccToL1 μ f) v) = σ.integrated μ (UnitaryRep.ccToL1 μ f) v := by
  have e := σ.map_comp_integrated μ h (UnitaryRep.ccToL1 μ f)
  have e2 : UnitaryRep.leftTranslate μ h (UnitaryRep.ccToL1 μ f) = UnitaryRep.ccToL1 μ f := by
    refine Lp.ext ?_
    have hc := (f.continuous.memLp_of_hasCompactSupport (μ := μ) (p := 1)
      f.hasCompactSupport).coeFn_toLp
    filter_upwards [UnitaryRep.coeFn_leftTranslate μ h (UnitaryRep.ccToL1 μ f), hc,
      (measurePreserving_mul_left μ h⁻¹).quasiMeasurePreserving.ae_eq_comp hc] with x h1 h2 h3
    rw [h1]
    change (UnitaryRep.ccToL1 μ f : normOneGL K n → ℂ) (h⁻¹ * x) = (UnitaryRep.ccToL1 μ f) x
    rw [show (UnitaryRep.ccToL1 μ f : normOneGL K n → ℂ) (h⁻¹ * x) = f (h⁻¹ * x) from h3,
      show (UnitaryRep.ccToL1 μ f : normOneGL K n → ℂ) x = f x from h2]
    exact hf x
  rw [e2] at e
  exact congrArg (fun A : H →L[ℂ] H => A v) e

theorem exists_fixedSubspace_ne_bot (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]
    (hσ : σ.IsIrreducible) :
    ∃ (U : Subgroup (AdelicGLn.integralFiniteGL K n))
      (hU : IsOpen (U : Set (AdelicGLn.integralFiniteGL K n))),
      fixedSubspace σ (openSubgroupOf U hU : Subgroup (AdelicGLn.FiniteAdelicGL K n)) ≠ ⊥ := by
  have := hσ.1
  obtain ⟨v, hv⟩ := exists_ne (0 : H)
  obtain ⟨g, hg⟩ := UnitaryRep.exists_integrated_ne_zero σ μ hv
  obtain ⟨f, hf, hfv⟩ : ∃ f, IsSmoothTest f ∧ σ.integrated μ (UnitaryRep.ccToL1 μ f) v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hg (UnitaryRep.integrated_eq_zero_of_dense σ μ IsSmoothTest
      (fun g' ε hε => exists_isSmoothTest_near μ g' hε) hcon g)
  obtain ⟨U, hU, hinv⟩ := hf.exists_finOne_mul
  refine ⟨U, hU, fun hbot => hfv ?_⟩
  have hmem : σ.integrated μ (UnitaryRep.ccToL1 μ f) v ∈
      fixedSubspace σ (openSubgroupOf U hU : Subgroup (AdelicGLn.FiniteAdelicGL K n)) := by
    rintro _ ⟨u, hu, rfl⟩
    rw [Subgroup.coe_subtype, finProj_eq_finOne]
    refine map_integrated_of_left_invariant (fun x => ?_) v
    rw [← map_inv]
    exact hinv u⁻¹ (U.inv_mem hu) x
  rw [hbot] at hmem
  exact (Submodule.mem_bot ℂ).1 hmem

end MultiplicityOne

end

end GroundTheory.Automorphic
