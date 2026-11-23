import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppendVMemFamAtlasTarget
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasPullbackEqChartExpression
open Set MeasureTheory
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.CxForm GlobalTheory.BcUnique
open scoped ContDiff Real Topology

namespace GlobalTheory.BcUnique

theorem loc_pullback_fib : ∀ (M : Type) [TopologicalSpace M] (A : HolAtlas M 1) (α : (famAtlas A).Fld), (famAtlas A).IsForm α → ∀ (j : A.ι) (k : sphere.ι) (t : OnePoint ℂ), t ∈ (sphere.e k).source → ∀ v : V 1, A.loc ((famAtlas A).pullback A (fib t) α) j v = pull headIn ((famAtlas A).loc α (j, k) (appendV 1 1 (v, sphere.e k t))) := by
  intro M _ A α hα j k t ht v
  by_cases hv : v ∈ (A.e j).target
  · have hs : (A.e j).symm v ∈ (A.e j).source := (A.e j).map_target hv
    have hr : A.e j ((A.e j).symm v) = v := (A.e j).right_inv hv
    have hm : fib t ((A.e j).symm v) ∈ ((famAtlas A).e (j, k)).source := ⟨hs, ht⟩
    have h1 : A.loc ((famAtlas A).pullback A (fib t) α) j (A.e j ((A.e j).symm v)) = _ :=
      A.loc_crd ((famAtlas A).pullback A (fib t) α) ⟨(j, (A.e j).symm v), hs⟩
    have h2 : (famAtlas A).loc α (j, k) (appendV 1 1 (A.e j ((A.e j).symm v), sphere.e k t)) = _ :=
      (famAtlas A).loc_crd α ⟨((j, k), fib t ((A.e j).symm v)), hm⟩
    rw [hr] at h1 h2
    have h3 := pullback_eq_chart _ _ _ _ (famAtlas A) A (fib t) α (isHolo_fib A t) hα
      ⟨(j, (A.e j).symm v), hs⟩ (j, k) hm
    have hev : ((famAtlas A).e (j, k) ∘ fib t ∘ (A.e j).symm) =ᶠ[𝓝 v]
        fun w => headIn w + appendV 1 1 (0, sphere.e k t) := by
      filter_upwards [(A.e j).open_target.mem_nhds hv] with w hw
      show appendV 1 1 (A.e j ((A.e j).symm w), sphere.e k t) = _
      rw [(A.e j).right_inv hw, headIn_apply, ← map_add]
      simp
    have hd : fderiv ℂ ((famAtlas A).e (j, k) ∘ fib t ∘ (A.e j).symm) (A.e j ((A.e j).symm v)) = headIn := by
      rw [hr, hev.fderiv_eq]
      exact (headIn.hasFDerivAt.add_const _).fderiv
    rw [h1, h2, h3]
    exact congrArg (fun L => pull L _) hd
  · have hn : appendV 1 1 (v, sphere.e k t) ∉ ((famAtlas A).e (j, k)).target := fun h =>
      hv ((appendV_mem_famAtlas_target A j k _ _).1 h).1
    simp only [HolAtlas.loc, dif_neg hv, dif_neg hn, map_zero]

end GlobalTheory.BcUnique
