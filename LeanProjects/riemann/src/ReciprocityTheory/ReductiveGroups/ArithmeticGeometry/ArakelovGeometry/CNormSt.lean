import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.FibreSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ChooseLePowDivFactorial
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.SupLeL2NormSections
import ReciprocityTheory.GeometryOfNumbers.SphericalMonomials.SupStMonoNormSqPos
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.LemCone

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Module Filter Asymptotics
open scoped ComplexOrder

variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] {D : ℕ}

theorem eval_smul_of_isHomogeneous {ι : Type*} {φ : MvPolynomial ι ℂ} {n : ℕ}
    (hφ : φ.IsHomogeneous n) (c : ℂ) (z : ι → ℂ) :
    eval (c • z) φ = c ^ n * eval z φ := by
  rw [eval_eq, eval_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hdeg : ∑ i ∈ m.support, m i = n := by
    have h := hφ (mem_support_iff.1 hm)
    simpa [Finsupp.weight_apply, Finsupp.sum] using h
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg]
  ring

theorem smul_mem_pts_coord {J : Type} [Fintype J] (x : J → Ω) {z : J → ℂ}
    (hz : z ∈ pts (coordIdeal ℤ x)) {c : ℂ} (hc : c ≠ 0) : c • z ∈ pts (coordIdeal ℤ x) := by
  refine ⟨smul_ne_zero hc hz.1, fun f hf => ?_⟩
  have hH := coordIdeal_isHomogIdeal ℤ x
  rw [← sum_homogeneousComponent f, map_sum, map_sum]
  refine Finset.sum_eq_zero fun d _ => ?_
  rw [eval_smul_of_isHomogeneous ((homogeneousComponent_isHomogeneous d f).map _),
    hz.2 _ (hH f hf d), mul_zero]

theorem dense_eval_ne_zero {N : ℕ} {Δ : MvPolynomial (Fin N) ℂ} (hΔ : Δ ≠ 0) :
    Dense {w | eval w Δ ≠ 0} := by
  rw [dense_iff_inter_open]
  rintro U hU ⟨w, hw⟩
  by_contra hne
  apply hΔ
  have h0 : ∀ v ∈ U, eval v Δ = 0 := fun v hv => by
    by_contra h
    exact hne ⟨v, hv, h⟩
  have han : AnalyticOnNhd ℂ (fun v => eval v Δ) Set.univ := AnalyticOnNhd.eval_mvPolynomial Δ
  have hz := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
    (Set.mem_univ w) (Filter.eventually_of_mem (hU.mem_nhds hw) h0)
  exact MvPolynomial.funext fun v => by simpa using hz (Set.mem_univ v)

theorem sec_sup_bdd {x : Ix κ → Ω} {m : ConeMetric ℂ (Ix κ)} {μ : Measure (Ix κ → ℂ)}
    (hg : IsGood D x m μ) (n : ℕ) (f : MvPolynomial (Ix κ) ℂ) (hf : f.IsHomogeneous n) :
    ∃ S : ℝ, ∀ z ∈ pts (coordIdeal ℤ x), ‖eval z f‖ ≤ S * m.ρ z ^ n := by
  classical
  have hρc : ContinuousOn m.ρ {z | z ≠ 0} := hg.semipos.1.continuousOn
  set K : Set (Ix κ → ℂ) := Metric.sphere 0 1 ∩
    {z | ∀ g ∈ coordIdeal ℤ x, eval z (map (Int.castRingHom ℂ) g) = 0} with hKdef
  have hcl : IsClosed {z : Ix κ → ℂ | ∀ g ∈ coordIdeal ℤ x,
      eval z (map (Int.castRingHom ℂ) g) = 0} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun g => isClosed_iInter fun _ =>
      isClosed_eq (continuous_eval _) continuous_const
  have hKc : IsCompact K := (isCompact_sphere 0 1).inter_right hcl
  have hsub : K ⊆ {z | z ≠ 0} := fun z hz h0 => by
    have := hz.1
    rw [mem_sphere_zero_iff_norm, h0, norm_zero] at this
    exact zero_ne_one this
  have hF : ContinuousOn (fun z => ‖eval z f‖ / m.ρ z ^ n) K :=
    (continuous_eval f).norm.continuousOn.div ((hρc.mono hsub).pow n)
      fun z hz => pow_ne_zero n (m.pos z (hsub hz)).ne'
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hF
  refine ⟨C, fun z hz => ?_⟩
  have ht : 0 < ‖z‖ := norm_pos_iff.mpr hz.1
  set c : ℂ := ((‖z‖⁻¹ : ℝ) : ℂ) with hcdef
  have hcn : ‖c‖ = ‖z‖⁻¹ := by
    rw [hcdef, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht)]
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, norm_zero] at hcn
    exact (inv_pos.mpr ht).ne' hcn.symm
  have hzK : c • z ∈ K := by
    refine ⟨?_, (smul_mem_pts_coord x hz hc0).2⟩
    rw [mem_sphere_zero_iff_norm, norm_smul, hcn, inv_mul_cancel₀ ht.ne']
  have h1 := hC _ hzK
  have hρ : 0 < m.ρ z := m.pos z hz.1
  have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc0
  rw [eval_smul_of_isHomogeneous hf, m.smul, norm_mul, norm_pow, mul_pow,
    mul_div_mul_left _ _ (pow_ne_zero n hcpos.ne'), Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (norm_nonneg _) (pow_nonneg hρ.le n))] at h1
  exact (div_le_iff₀ (pow_pos hρ n)).mp h1

theorem trace_sup_le {x : Ix κ → Ω} {m : ConeMetric ℂ (Ix κ)} {μ : Measure (Ix κ → ℂ)}
    (hg : IsGood D x m μ) {e : Fin (D + 1) → Ix κ} (hfr : IsProjFrame x e) (hFS : IsPullFS x e m)
    {n r : ℕ} (f : Fin r → MvPolynomial (Ix κ) ℤ) (g : Fin r → MvPolynomial (Fin (D + 1)) ℤ)
    (hf : ∀ k, (f k).IsHomogeneous n) (hgh : ∀ k, (g k).IsHomogeneous n)
    (htr : ∀ k, aeval (x ∘ e) (g k) = secTrace x e n (aeval x (f k))) (c : Fin r → ℂ) {S : ℝ}
    (hS : ∀ z ∈ pts (coordIdeal ℤ x),
      ‖∑ k, c k * eval z (map (Int.castRingHom ℂ) (f k))‖ ≤ S * m.ρ z ^ n)
    (w : Fin (D + 1) → ℂ) :
    ‖∑ k, c k * eval w (map (Int.castRingHom ℂ) (g k))‖ ≤
      (projDeg x e : ℝ) * S * Real.sqrt (sqN w) ^ n := by
  classical
  obtain ⟨Δ, hΔ0, hΔ⟩ := exists_isDiscr hfr
  have hFc : Continuous fun w : Fin (D + 1) → ℂ =>
      ‖∑ k, c k * eval w (map (Int.castRingHom ℂ) (g k))‖ :=
    (continuous_finsetSum _ fun k _ => continuous_const.mul (continuous_eval _)).norm
  have hGc : Continuous fun w : Fin (D + 1) → ℂ => (projDeg x e : ℝ) * S * Real.sqrt (sqN w) ^ n := by
    unfold sqN
    fun_prop
  have hgood : ∀ w ∈ {w : Fin (D + 1) → ℂ | eval w Δ ≠ 0},
      w ∈ {w : Fin (D + 1) → ℂ | ‖∑ k, c k * eval w (map (Int.castRingHom ℂ) (g k))‖ ≤
        (projDeg x e : ℝ) * S * Real.sqrt (sqN w) ^ n} := by
    intro w hw
    obtain ⟨hfin, hcard, -, htrace⟩ := hΔ w hw
    have hk : ∀ k, eval w (map (Int.castRingHom ℂ) (g k)) =
        ∑ z ∈ hfin.toFinset, eval z (map (Int.castRingHom ℂ) (f k)) := fun k => by
      rw [htrace n (f k) (g k) (hf k) (hgh k) (htr k), finsum_mem_eq_finite_toFinset_sum _ hfin]
    have hsum : ∑ k, c k * eval w (map (Int.castRingHom ℂ) (g k)) =
        ∑ z ∈ hfin.toFinset, ∑ k, c k * eval z (map (Int.castRingHom ℂ) (f k)) := by
      simp_rw [hk, Finset.mul_sum]
      exact Finset.sum_comm
    simp only [Set.mem_ofPred_eq]
    rw [hsum]
    refine (norm_sum_le _ _).trans ?_
    have hb : ∀ z ∈ hfin.toFinset,
        ‖∑ k, c k * eval z (map (Int.castRingHom ℂ) (f k))‖ ≤ S * Real.sqrt (sqN w) ^ n := by
      intro z hz
      rw [Set.Finite.mem_toFinset] at hz
      have h := hS z hz.1
      rwa [hFS z hz.1, show (∑ k, ‖z (e k)‖ ^ 2) = sqN w by simp [sqN, hz.2]] at h
    refine (Finset.sum_le_sum hb).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul, ← Set.ncard_eq_toFinset_card _ hfin, hcard, mul_assoc]
  have hcl := closure_minimal hgood (isClosed_le hFc hGc)
  rw [(dense_eval_ne_zero hΔ0).closure_eq] at hcl
  exact hcl (Set.mem_univ w)

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
