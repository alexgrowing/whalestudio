import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridge
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedE
import GroundTheory.HeightsAndTheta.Heights.Intersections.PtsIntegralLogNormRat
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsFurtherFurther
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsFurtherExtra
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M

namespace IntersectionWithSection

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]

omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)] in

theorem comp_mem_mcPts {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    {P' : Ideal (MRing ι')} {z' : (Σ k', ι' k') → ℂ} (hz : z' ∈ mcPts P') :
    (fun p => z' (v p)) ∈ mcPts (imageZ v P') := by
  refine ⟨fun k => ?_, fun f hf => ?_⟩
  · obtain ⟨i', hi'⟩ := hz.1 (κ k)
    obtain ⟨p, hp⟩ := hv.2.2.2 ⟨κ k, i'⟩ ⟨k, rfl⟩
    have h2 : p.1 = k := hv.1 (by rw [← hv.2.2.1 p, hp])
    obtain ⟨pk, pi⟩ := p
    simp only at h2
    subst h2
    exact ⟨pi, show z' (v ⟨pk, pi⟩) ≠ 0 by rw [hp]; exact hi'⟩
  · have h := hz.2 _ (Ideal.mem_comap.mp hf)
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_rename, eval_rename] at h
    exact h

theorem pullW_mem_fibre {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    {P' J' : Ideal (MRing ι')} {n : ℕ} (hP : IsArithVar (imageZ v P') (n + 1)) (R : AnLogRes P' J' n)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) {x : R.X}
    (h0 : Ψ (segre (pullPt R v x)) 0 ≠ 0) : pullW R v Ψ x ∈ fibre (imageZ v P') Ψ (pullQ R v Ψ x) := by
  classical
  obtain ⟨k0⟩ := hP.1
  let c : K → ℂ := Function.update (fun _ => (1 : ℂ)) k0 (Ψ (segre (pullPt R v x)) 0)⁻¹
  have hc : ∀ k, c k ≠ 0 := by
    intro k
    by_cases hk : k = k0
    · subst hk; simp [c, h0]
    · simp [c, Function.update_of_ne hk]
  have hpc : ∏ k, c k = (Ψ (segre (pullPt R v x)) 0)⁻¹ := by
    simp [c, Finset.prod_update_of_mem (Finset.mem_univ k0)]
  refine ⟨fun p => c p.1 * pullPt R v x p,
    mcPts_smul hP.2.1.2.1 c hc (comp_mem_mcPts hv (R.mem x x (R.mem_U x))), ?_, ?_⟩
  · rw [segre_smul, hpc]; rfl
  · funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [pullW, h0]
    · simp only [pullW, map_smul, Pi.smul_apply, smul_eq_mul, Fin.cons_succ, pullQ]
      rw [div_eq_inv_mul]

end IntersectionWithSection

open IntersectionWithSection in

theorem IntersectionWithSection.proof (hE : ResExistsStatement) (hPush : pullbackPushforward_holds.Statement)
    (hCount : PullbackDegreeCount.Statement) (hDens : pullbackDensity_holds.Statement) : IntersectionWithSection.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' n G J L L' A A' s hv hP' hP hJ hL hLL' hA hAA' hs
  classical
  have hA' := ArithmeticIntersectionIntegral.isSmoothHerm_pull hv hA hAA'
  have hL' : ∀ j, IsSmoothHerm (L' j) := fun j => ArithmeticIntersectionIntegral.isSmoothHerm_pull hv (hL j) (hLL' j)
  have hs' : IsSectionOn P' A' (rename v s) := by
    obtain ⟨a, hAa, hsa, hsP⟩ := hs
    refine ⟨Function.extend κ a 0, fun k' => ?_, ArithmeticIntersectionIntegral.isMultiHomog_rename hv hsa,
      fun h => hsP (Ideal.mem_comap.mpr h)⟩
    rw [hAA'.1, pullDeg]
    by_cases h : ∃ k, κ k = k'
    · obtain ⟨k, rfl⟩ := h
      rw [hv.1.extend_apply, hv.1.extend_apply, hAa k]
    · rw [Function.extend_apply' _ _ _ h, Function.extend_apply' _ _ _ h]
      simp
  obtain ⟨J', ⟨R⟩⟩ := exists_anLogRes hE hP'
  obtain ⟨Ψ, hΨ⟩ := goodProjExists K ι (imageZ v P') n hP
  obtain ⟨hnull, hfin⟩ := hPush K ι K' ι' κ v P' J' n R Ψ hv hP' hP hΨ
  rw [ptsIntegral_eq_mInt' hE resBridge R hP' hL' hA' hs', ptsIntegral_eq_at hE resBridge hP hΨ hL hA hs,
    pushForward_null R.A _ (fun j => potOf_isPotential R (L' j) (hL' j)) (pullQ R v Ψ) (pullBad R v Ψ) hnull
      (fun x hx j hj => by
        by_contra h
        exact hx (Or.inr ⟨j, hj, h⟩)) hfin _ (brIntegrable R L' A' (rename v s) hP' hL' hA' hs'),
    ptsIntegralAt, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [hCount K ι K' ι' κ v P' J' n G J R Ψ hv hP' hP hJ hΨ,
    hDens K ι K' ι' κ v P' J' n R Ψ L L' A A' s hv hP' hP hΨ hL hLL' hA hAA' hs] with y hc hd
  have hSf := hfin y
  have hFf := fibreFinite K ι (imageZ v P') n Ψ hP hΨ y
  have hmaps : ∀ x ∈ hSf.toFinset, pullW R v Ψ x ∈ hFf.toFinset := by
    intro x hx
    rw [Set.Finite.mem_toFinset] at hx ⊢
    have h0 : Ψ (segre (pullPt R v x)) 0 ≠ 0 := fun h => hx.2 (Or.inl (Or.inr h))
    have hw := pullW_mem_fibre hv hP R Ψ h0
    rwa [show pullQ R v Ψ x = y from hx.1] at hw
  rw [finsum_mem_eq_finite_toFinset_sum _ hSf, finsum_mem_eq_finite_toFinset_sum _ hFf, Finset.mul_sum]
  refine (Finset.sum_congr rfl fun x hx => hd x ((Set.Finite.mem_toFinset hSf).mp hx)).trans ?_
  rw [← Finset.sum_fiberwise_of_maps_to' hmaps]
  refine Finset.sum_congr rfl fun w hw => ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  congr 1
  have hset : ({x | pullQ R v Ψ x = y ∧ pullW R v Ψ x = w} \ pullBad R v Ψ) =
      ↑(hSf.toFinset.filter fun x => pullW R v Ψ x = w) := by
    ext x
    simp only [Finset.coe_filter, Set.Finite.mem_toFinset, Set.mem_sdiff, Set.mem_ofPred_eq, Set.mem_preimage,
      Set.mem_singleton_iff]
    tauto
  have hcw := hc w ((Set.Finite.mem_toFinset hFf).mp hw)
  rw [hset, Set.ncard_coe_finset] at hcw
  exact_mod_cast hcw

end GroundTheory.Heights₂.Heights.Inter
