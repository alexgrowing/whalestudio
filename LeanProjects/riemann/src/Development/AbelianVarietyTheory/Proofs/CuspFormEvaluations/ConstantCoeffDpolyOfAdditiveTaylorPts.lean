import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasSubstEv
import Development.AbelianVarietyTheory.Definitions.ThetaValues.MemAnalyticAtZeroOfEventuallyDifferentiableAt
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FormalExpMulFormalExpNeg

open Filter Topology MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory

section Comp

variable {σ τ W : Type*} [Fintype σ] [DecidableEq σ] [Fintype τ] [NormedAddCommGroup W]
  [NormedSpace ℂ W]

omit [DecidableEq σ] in

theorem hasSubst_taylorDir (u : τ → W) {φ : W → σ → ℂ} (h0 : φ 0 = 0) :
    HasSubst fun i => taylorDir u fun z => φ z i := by
  refine hasSubst_of_constantCoeff_zero fun i => ?_
  simp [h0]

private theorem fderiv_comp_apply_eq_sum_pi_single {φ : W → σ → ℂ} {f : (σ → ℂ) → ℂ} {z : W}
    (hφ : DifferentiableAt ℂ φ z) (hf : DifferentiableAt ℂ f (φ z)) (v : W) :
    fderiv ℂ (f ∘ φ) z v =
      ∑ i, fderiv ℂ f (φ z) (Pi.single i 1) * fderiv ℂ (fun y => φ y i) z v := by
  have hi : ∀ i, fderiv ℂ (fun y => φ y i) z v = fderiv ℂ φ z v i := fun i => by
    rw [(hasFDerivAt_pi'.1 hφ.hasFDerivAt i).fderiv]
    rfl
  simp_rw [hi]
  rw [fderiv_comp z hf hφ, ContinuousLinearMap.comp_apply]
  conv_lhs => rw [← Finset.univ_sum_single (fderiv ℂ φ z v)]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show (Pi.single i (fderiv ℂ φ z v i) : σ → ℂ) = fderiv ℂ φ z v i • Pi.single i 1 by
    ext k; by_cases h : k = i <;> simp [h], map_smul, smul_eq_mul, mul_comm]

private theorem taylorDir_comp_eq_subst_taylor_of_analyticAt (u : τ → W) {φ : W → σ → ℂ} (hφ : AnalyticAt ℂ φ 0)
    (h0 : φ 0 = 0) :
    ∀ D ∈ {D : MvPowerSeries τ ℂ | ∃ f : (σ → ℂ) → ℂ, AnalyticAt ℂ f 0 ∧
      D = taylorDir u (f ∘ φ) - subst (fun i => taylorDir u fun z => φ z i) (taylor f)}, D = 0 := by
  have hs : HasSubst fun i => taylorDir u fun z => φ z i := hasSubst_taylorDir u h0
  have ha0 : ∀ i, constantCoeff (taylorDir u fun z => φ z i) = 0 := fun i => by simp [h0]
  have hT : Tendsto φ (𝓝 0) (𝓝 0) := by simpa [h0] using hφ.continuousAt.tendsto
  have hφi : ∀ i, AnalyticAt ℂ (fun z => φ z i) 0 := fun i =>
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ℂ) i).analyticAt (φ 0)).comp hφ
  apply mvPowerSeries_eq_zero_of_pderiv_mem_span
  · rintro _ ⟨f, hf, rfl⟩
    rw [map_sub, FormalCalc.constantCoeff_subst_of_zero hs ha0]
    simp [h0]
  · rintro _ ⟨f, hf, rfl⟩ j
    have hfφ : AnalyticAt ℂ (f ∘ φ) 0 := hf.comp_of_eq hφ h0
    have hg : ∀ i, AnalyticAt ℂ (fun y => fderiv ℂ f y (Pi.single i 1)) 0 := fun i =>
      analyticAt_fderiv_apply hf _
    have hev : (fun z => fderiv ℂ (f ∘ φ) z (u j)) =ᶠ[𝓝 0] fun z => ∑ i,
        fderiv ℂ f (φ z) (Pi.single i 1) * fderiv ℂ (fun y => φ y i) z (u j) := by
      filter_upwards [hφ.eventually_analyticAt, hT.eventually hf.eventually_analyticAt] with z hz1 hz2
      exact fderiv_comp_apply_eq_sum_pi_single hz1.differentiableAt hz2.differentiableAt (u j)
    have hsum := taylorDir_sum u Finset.univ (F := fun i z =>
        fderiv ℂ f (φ z) (Pi.single i 1) * fderiv ℂ (fun y => φ y i) z (u j))
      (fun i _ => ((hg i).comp_of_eq hφ h0).mul (analyticAt_fderiv_apply (hφi i) _))
    beta_reduce at hsum
    have key : pderiv ℂ j (taylorDir u (f ∘ φ) -
        subst (fun i => taylorDir u fun z => φ z i) (taylor f)) =
        ∑ i, (taylorDir u ((fun y => fderiv ℂ f y (Pi.single i 1)) ∘ φ) -
          subst (fun i => taylorDir u fun z => φ z i) (taylor fun y => fderiv ℂ f y (Pi.single i 1))) *
            pderiv ℂ j (taylorDir u fun z => φ z i) := by
      rw [map_sub, FormalCalc.pderiv_subst hs, ← taylorDir_fderiv u hfφ j, taylorDir_congr u hev,
        hsum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [sub_mul, ← taylorDir_fderiv u (hφi i) j, taylor_fderiv hf i]
      congr 1
      exact taylorDir_mul u ((hg i).comp_of_eq hφ h0) (analyticAt_fderiv_apply (hφi i) _)
    rw [key]
    exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _
      (Ideal.subset_span ⟨_, hg i, rfl⟩)

theorem taylorDir_comp (u : τ → W) {φ : W → σ → ℂ} (hφ : AnalyticAt ℂ φ 0) (h0 : φ 0 = 0)
    {f : (σ → ℂ) → ℂ} (hf : AnalyticAt ℂ f 0) :
    taylorDir u (f ∘ φ) = subst (fun i => taylorDir u fun z => φ z i) (taylor f) := by
  have hs : HasSubst fun i => taylorDir u fun z => φ z i := hasSubst_taylorDir u h0
  have hD := taylorDir_comp_eq_subst_taylor_of_analyticAt u hφ h0 (taylorDir u (f ∘ φ) -
    subst (fun i => taylorDir u fun z => φ z i) (taylor f)) ⟨f, hf, rfl⟩
  exact sub_eq_zero.1 hD

end Comp

section Points

variable {n d : ℕ} {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]

variable (e : Fin 1 × Fin d → W) {f : W → ℂ}

variable {ι : Type} [Fintype ι]

end Points

section Curried

variable {m n d d' : ℕ}

noncomputable def taylorPts (n : ℕ) (F : (Fin n → Fin d → ℂ) → ℂ) : PS ℂ n d :=
  taylor fun z : Fin n × Fin d → ℂ => F fun j i => z (j, i)

noncomputable def curryPts (n d : ℕ) : (Fin n × Fin d → ℂ) →L[ℂ] (Fin n → Fin d → ℂ) :=
  ContinuousLinearMap.pi fun j => ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (j, i)

@[simp] theorem curryPts_apply (z : Fin n × Fin d → ℂ) (j : Fin n) (i : Fin d) :
    curryPts n d z j i = z (j, i) := rfl

@[simp] theorem constantCoeff_taylorPts (F : (Fin n → Fin d → ℂ) → ℂ) :
    constantCoeff (taylorPts n F) = F 0 := by
  unfold taylorPts
  rw [constantCoeff_taylor]
  rfl

@[simp] theorem taylorPts_coord (j : Fin n) (i : Fin d) :
    taylorPts n (fun z : Fin n → Fin d → ℂ => z j i) = X (j, i) := taylor_coord (j, i)

@[simp] theorem taylorPts_const (c : ℂ) :
    taylorPts n (fun _ : Fin n → Fin d → ℂ => c) = C c := taylor_const c

section Algebra

variable {F G : (Fin n → Fin d → ℂ) → ℂ}

end Algebra

end Curried

end GlobalTheory
