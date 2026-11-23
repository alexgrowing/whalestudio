import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.IteratedFDerivEqZeroOfIsBigO
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.ZeroDimA

namespace ReciprocityTheory.ChartRestriction.G.AR

open Filter Topology Asymptotics ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open scoped ContDiff

noncomputable section

theorem multilinear_diagonal_homogeneous {n a : ℕ} (D : ContinuousMultilinearMap ℂ (fun _ : Fin a => V n) ℂ) :
    ∃ b : (Fin n → ℕ) → ℂ, ∀ u : V n,
      D (fun _ => u) = ∑ α ∈ Finset.Nat.antidiagonalTuple n a, b α * ∏ k, u k ^ α k := by
  classical
  let cnt : (Fin a → Fin n) → Fin n → ℕ := fun r k => (Finset.univ.filter fun i => r i = k).card
  refine ⟨fun α => ∑ r ∈ Finset.univ.filter (fun r => cnt r = α),
    D (fun i => EuclideanSpace.single (r i) (1 : ℂ)), fun u => ?_⟩
  have hu : u = ∑ k, u k • EuclideanSpace.single k (1 : ℂ) := by
    simpa using ((EuclideanSpace.basisFun (Fin n) ℂ).toBasis.sum_repr u).symm
  have h1 : D (fun _ => u) =
      ∑ r : Fin a → Fin n, (∏ i, u (r i)) * D (fun i => EuclideanSpace.single (r i) (1 : ℂ)) := by
    have e1 : (fun _ : Fin a => u) = fun _ => ∑ k, u k • EuclideanSpace.single k (1 : ℂ) := by
      rw [← hu]
    rw [e1, D.map_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [D.map_smul_univ (fun i => u (r i)) (fun i => EuclideanSpace.single (r i) (1 : ℂ)), smul_eq_mul]
  have h2 : ∀ r : Fin a → Fin n, ∏ i, u (r i) = ∏ k, u k ^ cnt r k := by
    intro r
    rw [← Finset.prod_fiberwise Finset.univ r (fun i => u (r i))]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [Finset.prod_congr rfl (g := fun _ => u k) fun i hi => by rw [(Finset.mem_filter.1 hi).2],
      Finset.prod_const]
  have hmap : ∀ r ∈ (Finset.univ : Finset (Fin a → Fin n)), cnt r ∈ Finset.Nat.antidiagonalTuple n a := by
    intro r _
    rw [Finset.Nat.mem_antidiagonalTuple]
    have := Finset.card_eq_sum_card_fiberwise (s := Finset.univ) (t := Finset.univ) (f := r)
      (fun i _ => Finset.mem_univ (r i))
    simpa [cnt] using this.symm
  rw [h1, ← Finset.sum_fiberwise_of_maps_to hmap]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [h2 r, (Finset.mem_filter.1 hr).2]
  exact mul_comm _ _

theorem taylor_expansion_at_origin {n a : ℕ} (G : V n → ℂ) (U : Set (V n)) (hU : IsOpen U) (h0 : (0 : V n) ∈ U)
    (hG : DifferentiableOn ℂ G U) (hO : G =O[𝓝 0] fun u => ‖u‖ ^ a) :
    ∃ b : (Fin n → ℕ) → ℂ,
      (fun u => G u - ∑ α ∈ Finset.Nat.antidiagonalTuple n a, b α * ∏ k, u k ^ α k)
        =O[𝓝 0] fun u => ‖u‖ ^ (a + 1) := by
  have hc : ContDiffOn ℂ ∞ G U := contDiffOn_of_differentiableOn n G U hU hG
  set D := iteratedFDeriv ℂ a G 0 with hD
  set M := (a.factorial : ℂ)⁻¹ • D with hM
  obtain ⟨b, hb⟩ := multilinear_diagonal_homogeneous M
  refine ⟨b, ?_⟩
  set p : V n → ℂ := fun u => M (fun _ => u) with hp
  have hpc : ContDiff ℂ ∞ p := M.contDiff.comp (contDiff_pi.2 fun _ => contDiff_id)
  have hpO : p =O[𝓝 0] fun u => ‖u‖ ^ a := by
    refine IsBigO.of_bound ‖M‖ (Eventually.of_forall fun u => ?_)
    rw [norm_pow, norm_norm]
    have := M.le_opNorm (fun _ => u)
    simpa [Finset.prod_const] using this
  set H : V n → ℂ := fun u => G u - p u with hH
  have hHc : ContDiffOn ℂ ∞ H U := hc.sub hpc.contDiffOn
  have hHO : H =O[𝓝 0] fun u => ‖u‖ ^ a := hO.sub hpO
  have hcG : ContDiffAt ℂ a G 0 := (hc.contDiffAt (hU.mem_nhds h0)).of_le (by exact_mod_cast le_top)
  have hcp : ContDiffAt ℂ a p 0 := hpc.contDiffAt.of_le (by exact_mod_cast le_top)
  have hpa : iteratedFDeriv ℂ a p 0 = D := by
    ext v
    rw [hp, M.iteratedFDeriv_comp_diagonal]
    have hs : ∀ σ : Equiv.Perm (Fin a), M (fun i => v (σ i)) = M v := by
      intro σ
      simp only [hM, ContinuousMultilinearMap.smul_apply]
      congr 1
      exact zd_iteratedFDeriv_comp_perm hU hc a 0 h0 σ v
    rw [Finset.sum_congr rfl (fun σ _ => hs σ), Finset.sum_const, Finset.card_univ,
      Fintype.card_perm, Fintype.card_fin, hM, ContinuousMultilinearMap.smul_apply, nsmul_eq_mul,
      smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast (Nat.factorial_pos a).ne'), one_mul]
  have hzero : ∀ k < a + 1, iteratedFDeriv ℂ k H 0 = 0 := by
    intro k hk
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · obtain ⟨m, rfl⟩ : ∃ m, a = m + 1 := ⟨a - 1, by omega⟩
      exact iteratedFDeriv_eq_zero_of_isBigO_alt m H U 0 hU h0 hHc (by simpa using hHO) k (by omega)
    · rw [hH, show (fun u => G u - p u) = G - p from rfl, iteratedFDeriv_sub_apply hcG hcp, hpa,
        sub_self]
  have := isBigO_pow_of_iteratedFDeriv_zero (a + 1) H U 0 hU h0 hHc hzero
  refine (this.congr_left fun u => ?_).congr_right fun u => by rw [sub_zero]
  simp only [hH, hp, hb]

theorem taylor_expansion_local_coordinates {n a : ℕ} (g : V n → ℂ) (ζ : V n → V n) (U : Set (V n)) (x : V n)
    (hU : IsOpen U) (hx : x ∈ U) (hg : DifferentiableOn ℂ g U) (hζ : DifferentiableOn ℂ ζ U)
    (hζ0 : ζ x = 0) (hdet : (fderiv ℂ ζ x).det ≠ 0) (hO : g =O[𝓝 x] fun v => ‖v - x‖ ^ a) :
    ∃ b : (Fin n → ℕ) → ℂ,
      (fun v => g v - ∑ α ∈ Finset.Nat.antidiagonalTuple n a, b α * ∏ k, ζ v k ^ α k)
        =O[𝓝 x] fun v => ‖v - x‖ ^ (a + 1) := by
  have hcζ : ContDiffOn ℂ ∞ ζ U := contDiffOn_euclidean.2 fun k =>
    contDiffOn_of_differentiableOn n _ U hU (differentiableOn_euclidean.1 hζ k)
  have hCA : ContDiffAt ℂ 1 ζ x := (hcζ.contDiffAt (hU.mem_nhds hx)).of_le (by exact_mod_cast le_top)
  let E : V n ≃L[ℂ] V n :=
    (LinearMap.equivOfDetNeZero (fderiv ℂ ζ x : V n →ₗ[ℂ] V n) hdet).toContinuousLinearEquiv
  have hE : (E : V n →L[ℂ] V n) = fderiv ℂ ζ x := ContinuousLinearMap.ext fun _ => rfl
  have hf' : HasFDerivAt ζ (E : V n →L[ℂ] V n) x := by
    rw [hE]; exact (hζ.differentiableAt (hU.mem_nhds hx)).hasFDerivAt
  set ψ := hCA.localInverse hf' one_ne_zero with hψ
  have hψ0 : ψ 0 = x := by rw [← hζ0]; exact hCA.localInverse_apply_image hf' one_ne_zero
  have hψC : ContDiffAt ℂ 1 ψ 0 := by rw [← hζ0]; exact hCA.to_localInverse hf' one_ne_zero
  have hleft : ∀ᶠ v in 𝓝 x, ψ (ζ v) = v := (hCA.hasStrictFDerivAt' hf' one_ne_zero).eventually_left_inverse
  have hψt : Tendsto ψ (𝓝 0) (𝓝 x) := by
    have := hψC.continuousAt.tendsto; rwa [hψ0] at this
  have hSn : {u | DifferentiableAt ℂ ψ u ∧ ψ u ∈ U} ∈ 𝓝 (0 : V n) :=
    ((hψC.eventually (by simp)).mono fun u hu => hu.differentiableAt one_ne_zero).and
      (hψt.eventually (hU.mem_nhds hx))
  set U' := interior {u | DifferentiableAt ℂ ψ u ∧ ψ u ∈ U}
  have hG : DifferentiableOn ℂ (g ∘ ψ) U' := fun u hu =>
    have hu' := interior_subset hu
    ((hg.differentiableAt (hU.mem_nhds hu'.2)).comp u hu'.1).differentiableWithinAt
  have hψd : HasFDerivAt ψ (fderiv ℂ ψ 0) 0 := (hψC.differentiableAt one_ne_zero).hasFDerivAt
  have hGO : (g ∘ ψ) =O[𝓝 0] fun u => ‖u‖ ^ a := by
    refine (hO.comp_tendsto hψt).trans ?_
    have h1 := hψd.isBigO_sub
    rw [hψ0] at h1
    simp only [sub_zero] at h1
    exact h1.norm_norm.pow a
  obtain ⟨b, hb⟩ := taylor_expansion_at_origin (g ∘ ψ) U' isOpen_interior (mem_interior_iff_mem_nhds.2 hSn) hG hGO
  refine ⟨b, ?_⟩
  have hζt : Tendsto ζ (𝓝 x) (𝓝 0) := by
    have := (hζ.differentiableAt (hU.mem_nhds hx)).continuousAt.tendsto; rwa [hζ0] at this
  have hζO : (fun v => ζ v) =O[𝓝 x] fun v => v - x := by
    have := (hζ.differentiableAt (hU.mem_nhds hx)).hasFDerivAt.isBigO_sub
    simpa [hζ0] using this
  refine ((hb.comp_tendsto hζt).congr' (hleft.mono fun v hv => ?_) EventuallyEq.rfl).trans ?_
  · simp [hv]
  · exact hζO.norm_norm.pow (a + 1)

end

end ReciprocityTheory.ChartRestriction.G.AR
