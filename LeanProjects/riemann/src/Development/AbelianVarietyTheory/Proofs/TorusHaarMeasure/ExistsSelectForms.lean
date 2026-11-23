import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalExponentialDecay
import ReciprocityTheory.L2DbarEstimates.LeviForms.LogNormSq
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.HoloSmooth

open ReciprocityTheory.L2DbarEstimates Topology
open scoped ContDiff Matrix

namespace GlobalTheory.LeviRank

theorem exists_select_forms {K M : Type} [Field K] [AddCommGroup M] [Module K M]
    [FiniteDimensional K M] {n N : ℕ} (hn : Module.finrank K M = n)
    (φ : Fin N → Module.Dual K M) (hφ : ∀ x, (∀ k, φ k x = 0) → x = 0) :
    ∃ jj : Fin n → Fin N, ∀ x, (∀ k, φ (jj k) x = 0) → x = 0 := by
  classical
  have hspan : Submodule.span K (Set.range φ) = ⊤ := by
    rw [eq_top_iff]
    intro f _
    apply mem_span_of_iInf_ker_le_ker
    intro x hx
    have : x = 0 := hφ x (fun k => by simpa using (Submodule.mem_iInf _).1 hx k)
    simp [this]
  obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent' K φ
  have : Finite κ := Finite.of_injective a ha
  let : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card κ = n := by
    have h := finrank_span_eq_card hli
    rw [hsp, hspan, finrank_top, Subspace.dual_finrank_eq, hn] at h
    exact h.symm
  let e : κ ≃ Fin n := Fintype.equivFinOfCardEq hcard
  refine ⟨fun k => a (e.symm k), fun x hx => hφ x fun k => ?_⟩
  have hk : φ k ∈ Submodule.span K (Set.range (φ ∘ a)) := by rw [hsp, hspan]; trivial
  refine Submodule.span_induction (p := fun f _ => f x = 0) ?_ ?_ ?_ ?_ hk
  · rintro _ ⟨i, rfl⟩
    simpa using hx (e i)
  · simp
  · intro f g _ _ hf hg; simp [hf, hg]
  · intro c f _ hf; simp [hf]

theorem wJac_mulVec {n N : ℕ} (w : Fin N → V n → ℂ) (x : V n)
    (hw : ∀ k, DifferentiableAt ℂ (w k) x) (ξ : V n) (k : Fin N) :
    (wJac n N w x *ᵥ ξ.ofLp) k = fderiv ℂ (w k) x ξ := by
  have hξ : ξ = ∑ j, ξ.ofLp j • bas n j := by
    ext i
    simp [bas, Pi.single_apply]
  conv_rhs => rw [hξ]
  simp only [wJac, Matrix.mulVec, dotProduct, wd_of_differentiableAt (hw k), map_sum, map_smul,
    smul_eq_mul]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem main : ∀ (n N : ℕ) (w : Fin N → V n → ℂ) (U : Set (V n)), IsOpen U → (0 : V n) ∈ U →
    (∀ k, DifferentiableOn ℂ (w k) U) → (∃ k, w k 0 ≠ 0) →
    (∀ ξ : Fin n → ℂ, ξ ≠ 0 → 0 < (leviV n (fun z => ((Real.log (∑ k, ‖w k z‖ ^ 2) : ℝ) : ℂ)) 0 ξ).re) →
    ∃ (j0 : Fin N) (jj : Fin n → Fin N), w j0 0 ≠ 0 ∧
      (fderiv ℂ (fun z : V n => (WithLp.toLp 2 fun k => w (jj k) z / w j0 z : V n)) 0).det ≠ 0 := by
  intro n N w U hU h0 hw ⟨j0, hj0⟩ hL
  have hC : ∀ k, ContDiffAt ℂ 2 (w k) 0 := fun k =>
    ((contDiffOn_of_differentiableOn n (w k) U hU (hw k)).contDiffAt (hU.mem_nhds h0)).of_le
      (WithTop.coe_le_coe.2 le_top)
  have hD : ∀ k, DifferentiableAt ℂ (w k) 0 := fun k => (hw k).differentiableAt (hU.mem_nhds h0)
  have hne : (fun i => w i 0) ≠ 0 := fun h => hj0 (congrFun h j0)
  have hQ : ∀ k, DifferentiableAt ℂ (fun z => w k z / w j0 z) 0 := fun k => by
    simp only [div_eq_mul_inv]
    exact (hD k).mul ((differentiableAt_inv hj0).comp (0 : V n) (hD j0))
  have hker : ∀ x : V n, (∀ k, fderiv ℂ (fun z => w k z / w j0 z) 0 x = 0) → x = 0 := by
    intro x hx
    by_contra hx0
    have hξ : x.ofLp ≠ 0 := fun h => hx0 (by ext i; simpa using congrFun h i)
    have h1 := hL _ hξ
    have e1 : (fun z => ((Real.log (∑ k, ‖w k z‖ ^ 2) : ℝ) : ℂ)) =
        fun y => ((Real.log (sqNorm (fun i => w i y)) : ℝ) : ℂ) := by
      funext y; simp [sqNorm, Complex.normSq_eq_norm_sq]
    rw [e1, leviLogNormSq n N w 0 x.ofLp hC hne] at h1
    have hJ : wJac n N w 0 *ᵥ x.ofLp = (fderiv ℂ (w j0) 0 x / w j0 0) • fun i => w i 0 := by
      funext k
      rw [wJac_mulVec w 0 hD]
      have hev : w k =ᶠ[𝓝 0] fun z => (w k z / w j0 z) * w j0 z := by
        filter_upwards [(hD j0).continuousAt.eventually_ne hj0] with z hz
        rw [div_mul_cancel₀ _ hz]
      rw [hev.fderiv_eq, fderiv_fun_mul (hQ k) (hD j0)]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, hx k, smul_eq_mul,
        Pi.smul_apply]
      ring
    have hs : ((sqNorm (fun i => w i 0) : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.2 (sqNorm_pos hne).ne'
    have hP : projPerp (fun i => w i 0) *ᵥ (fun i => w i 0) = 0 := by
      rw [projPerp_mulVec, star_dotProduct_self, inv_mul_cancel₀ hs, one_smul, sub_self]
    rw [hJ, Matrix.mulVec_smul, hP, smul_zero] at h1
    simp [sqNorm] at h1
  obtain ⟨jj, hjj⟩ := exists_select_forms (K := ℂ) (M := V n) (n := n) (by simp)
    (fun k => (fderiv ℂ (fun z => w k z / w j0 z) 0 : V n →L[ℂ] ℂ).toLinearMap) hker
  refine ⟨j0, jj, hj0, ?_⟩
  have hF : DifferentiableAt ℂ
      (fun z : V n => (WithLp.toLp 2 fun k => w (jj k) z / w j0 z : V n)) 0 :=
    differentiableAt_euclidean.2 fun k => hQ (jj k)
  rw [ContinuousLinearMap.det, Ne, LinearMap.det_eq_zero_iff_ker_ne_bot, not_not,
    LinearMap.ker_eq_bot']
  intro x hx
  refine hjj x fun k => ?_
  have h2 := ((EuclideanSpace.proj (𝕜 := ℂ) k : V n →L[ℂ] ℂ).hasFDerivAt.comp (0 : V n)
    hF.hasFDerivAt).fderiv
  have h3 : (fun z => w (jj k) z / w j0 z) = (EuclideanSpace.proj (𝕜 := ℂ) k : V n →L[ℂ] ℂ) ∘
      (fun z : V n => (WithLp.toLp 2 fun k => w (jj k) z / w j0 z : V n)) := rfl
  change fderiv ℂ (fun z => w (jj k) z / w j0 z) 0 x = 0
  rw [h3, h2, ContinuousLinearMap.comp_apply]
  change (EuclideanSpace.proj (𝕜 := ℂ) k : V n →L[ℂ] ℂ) (((fderiv ℂ (fun z : V n => (WithLp.toLp 2 fun k => w (jj k) z / w j0 z : V n)) 0 : V n →L[ℂ] V n) : V n →ₗ[ℂ] V n) x) = 0
  rw [hx, map_zero]

end GlobalTheory.LeviRank
