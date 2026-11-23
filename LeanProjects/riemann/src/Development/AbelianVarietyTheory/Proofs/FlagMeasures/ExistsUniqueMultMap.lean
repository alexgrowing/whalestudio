import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.TopfBasis
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsCuspHom
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExtAeEqContRep
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicTransportMeasureFirst
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicTransportMeasureThird

open MeasureTheory Formalism.MainNotions.S Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.RowLev NumberField Matrix
open scoped InnerProductSpace TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IntertwMult

theorem contRep_facts (I : AutInst) (μf : Measure I.Gf) [μf.IsHaarMeasure] [SigmaFinite μf] (fund : Set I.GA)
    (R : I.GA → (I.L2 μf fund →L[ℂ] I.L2 μf fund)) (hF : I.IsFundDom (I.muA μf) fund)
    (hR : I.IsRightReg μf fund R) (y : I.L2 μf fund) (f : I.GA → ℂ) (hc : Continuous f)
    (hi : ∀ γ ∈ I.GFset, ∀ x, f (γ * x) = f x) (he : ∀ᵐ x ∂(I.muA μf), f x = I.ext y x) :
    (∀ f' : I.GA → ℂ, Continuous f' → (∀ᵐ x ∂(I.muA μf), f' x = I.ext y x) → f' = f) ∧
    (I.IsCuspFn (I.muA μf) (I.ext y) → I.IsCuspFn (I.muA μf) f) ∧
    ∀ (k : I.GA) (c : ℂ), R k y = c • y → ∀ x, f (x * k) = c * f x := by
  classical
  have hH : I.IsHilbTensor (H := fun _ => ℂ) (fun _ _ => ContinuousLinearMap.id ℂ ℂ)
      (fun _ => ContinuousLinearMap.id ℂ ℂ) (fun x => ∏ v, x v) := by
    refine ⟨fun x y => ?_, fun _ _ => rfl, ?_⟩
    · simp only [RCLike.inner_apply, map_prod, ← Finset.prod_mul_distrib]
    · have hspan : Submodule.span ℂ (Set.range fun x : (∀ _ : InfinitePlace I.F, ℂ) => ∏ v, x v) = ⊤ := by
        refine eq_top_iff.2 fun z _ => ?_
        have h1 : (1 : ℂ) ∈ Set.range fun x : (∀ _ : InfinitePlace I.F, ℂ) => ∏ v, x v :=
          ⟨fun _ => 1, by simp⟩
        simpa using Submodule.smul_mem _ z (Submodule.subset_span h1)
      rw [hspan, Submodule.top_coe]
      exact dense_univ
  let B : RowsAut := GlobalTheory.RepSmooth.bundle I μf fund R (fun _ => ℂ) (fun _ => inferInstance)
    (fun _ _ => ContinuousLinearMap.id ℂ ℂ) ℂ (fun _ => ContinuousLinearMap.id ℂ ℂ) (fun x => ∏ v, x v) hF hR hH 1
  have hy : GlobalTheory.Dec.IsContRep B y f := GlobalTheory.RepSmooth.isContRep_of_ae B hc hi he
  obtain ⟨-, -, htr, hfin⟩ := GlobalTheory.ExtContRep.ext_ae_eq_contRep B y f hy
  obtain ⟨huniq, hlin, -, -⟩ := GlobalTheory.ContRepUniq.contRep_unique_linear B
  refine ⟨fun f' hc' he' => ?_, fun hcu W hW ν hν => ?_, fun k c hk x => ?_⟩
  · have hae : ∀ᵐ x ∂(I.muA μf), f' x = f x := by
      filter_upwards [he', he] with x h1 h2
      rw [h1, h2]
    exact GlobalTheory.RepSmooth.eq_of_ae B hc' hc hae
  · haveI : IsFiniteMeasure ν := hν.1
    filter_upwards [hcu W hW ν hν, hfin ν inferInstance] with x h1 h2
    have h2' : ∀ᵐ m ∂ν, I.ext y (m * x) = f (m * x) := h2
    rw [← h1]
    exact integral_congr_ae (h2'.mono fun m hm => hm.symm)
  · have h3 : GlobalTheory.Dec.IsContRep B (R k y) (fun x => f (x * k)) := htr k
    rw [hk] at h3
    have h4 := hlin y y f f (c - 1) hy hy
    have e1 : y + (c - 1) • y = c • y := by
      rw [sub_smul, one_smul, add_sub_cancel]
    rw [e1] at h4
    have h5 : f (x * k) = f x + (c - 1) * f x := congrFun (huniq _ _ _ h3 h4) x
    rw [h5]
    ring

end GlobalTheory.IntertwMult
