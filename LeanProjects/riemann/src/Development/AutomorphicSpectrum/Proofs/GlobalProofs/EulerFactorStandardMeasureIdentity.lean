import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CoefS
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct ENNReal

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.TailProduct

private theorem abs_finset_prod_sub_one_le {κ : Type} (f : κ → ℝ) (s : Finset κ) :
    |(∏ v ∈ s, f v) - 1| ≤ (∏ v ∈ s, (1 + |f v - 1|)) - 1 := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a s ha ih
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have h1 : |f a| ≤ 1 + |f a - 1| := by
      have := abs_sub_abs_le_abs_sub (f a) 1
      rw [abs_one] at this
      linarith
    have hfa : f a * (∏ v ∈ s, f v) - 1 = f a * ((∏ v ∈ s, f v) - 1) + (f a - 1) := by ring
    rw [hfa]
    calc |f a * ((∏ v ∈ s, f v) - 1) + (f a - 1)|
        ≤ |f a| * |(∏ v ∈ s, f v) - 1| + |f a - 1| := by
          rw [← abs_mul]
          exact abs_add_le _ _
      _ ≤ (1 + |f a - 1|) * ((∏ v ∈ s, (1 + |f v - 1|)) - 1) + |f a - 1| := by
          gcongr
      _ = (1 + |f a - 1|) * (∏ v ∈ s, (1 + |f v - 1|)) - 1 := by ring

theorem abs_tprod_sub_one_le {κ : Type} (f : κ → ℝ)
    (hs : Summable (fun v => |f v - 1|)) :
    |(∏' v, f v) - 1| ≤ Real.exp (∑' v, |f v - 1|) - 1 := by
  have hm : Multipliable f := by
    have h := multipliable_one_add_of_summable (f := fun v => f v - 1)
      (by simpa only [Real.norm_eq_abs] using hs)
    simpa only [add_sub_cancel] using h
  have ht : Filter.Tendsto (fun s : Finset κ => ∏ v ∈ s, f v) Filter.atTop
      (nhds (∏' v, f v)) := hm.hasProd
  have hb : ∀ s : Finset κ, |(∏ v ∈ s, f v) - 1| ≤ Real.exp (∑' v, |f v - 1|) - 1 := by
    intro s
    refine (abs_finset_prod_sub_one_le f s).trans ?_
    gcongr ?_ - 1
    calc ∏ v ∈ s, (1 + |f v - 1|) ≤ ∏ v ∈ s, Real.exp (|f v - 1|) := by
          apply Finset.prod_le_prod
          · intro i _
            positivity
          · intro i _
            have := Real.add_one_le_exp (|f i - 1|)
            linarith
      _ = Real.exp (∑ v ∈ s, |f v - 1|) := (Real.exp_sum s _).symm
      _ ≤ Real.exp (∑' v, |f v - 1|) :=
          Real.exp_le_exp.mpr (hs.sum_le_tsum s (fun i _ => abs_nonneg _))
  exact le_of_tendsto' ((continuous_abs.tendsto _).comp (ht.sub_const 1)) hb

theorem tendsto_tprod_compl_one {ι : Type} (f : ι → ℝ)
    (hs : Summable (fun v => |f v - 1|)) :
    Filter.Tendsto (fun S : Finset ι => ∏' v : {v // v ∉ S}, f v) Filter.atTop (nhds 1) := by
  have hb : ∀ S : Finset ι, ‖(∏' v : {v // v ∉ S}, f v) - 1‖ ≤
      Real.exp (∑' v : {v // v ∉ S}, |f v - 1|) - 1 := by
    intro S
    rw [Real.norm_eq_abs]
    exact GlobalTheory.CompanionTheory.Hypotheses₂.OneV.TailProduct.abs_tprod_sub_one_le (fun v : {v // v ∉ S} => f v) (hs.subtype _)
  have hlim : Filter.Tendsto (fun S : Finset ι => Real.exp (∑' v : {v // v ∉ S}, |f v - 1|) - 1)
      Filter.atTop (nhds 0) := by
    have h := ((Real.continuous_exp.tendsto 0).comp
      (tendsto_tsum_compl_atTop_zero (fun v => |f v - 1|))).sub_const 1
    simpa [Function.comp_def, Real.exp_zero] using h
  have h0 := squeeze_zero_norm hb hlim
  simpa using h0.add_const 1

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.TailProduct
