import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ABridgeSt

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Module Filter Asymptotics
open scoped ComplexOrder Topology

variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] {D : ℕ}

theorem interp_rho (m₀ m₁ : ConeMetric ℂ (Ix κ)) (t : ℝ) (z : Ix κ → ℂ) :
    (interp m₀ m₁ t).ρ z = m₀.ρ z ^ (1 - t) * m₁.ρ z ^ t := rfl

theorem fderiv2_lin_comb {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {S : Set E} (hS : IsOpen S)
    {f g h : E → ℝ} (a b : ℝ) (hf : ContDiffOn ℝ 2 f S) (hg : ContDiffOn ℝ 2 g S)
    (hh : ∀ y ∈ S, h y = a * f y + b * g y) {z : E} (hz : z ∈ S) :
    fderiv ℝ (fderiv ℝ h) z = a • fderiv ℝ (fderiv ℝ f) z + b • fderiv ℝ (fderiv ℝ g) z := by
  have hfz : ∀ y ∈ S, ContDiffAt ℝ 2 f y := fun y hy => hf.contDiffAt (hS.mem_nhds hy)
  have hgz : ∀ y ∈ S, ContDiffAt ℝ 2 g y := fun y hy => hg.contDiffAt (hS.mem_nhds hy)
  have e1 : fderiv ℝ h =ᶠ[𝓝 z] fun y => a • fderiv ℝ f y + b • fderiv ℝ g y := by
    filter_upwards [hS.mem_nhds hz] with y hy
    have hfd : DifferentiableAt ℝ f y := (hfz y hy).differentiableAt (by first | norm_num | simp)
    have hgd : DifferentiableAt ℝ g y := (hgz y hy).differentiableAt (by first | norm_num | simp)
    have hev : h =ᶠ[𝓝 y] fun w => a * f w + b * g w := by
      filter_upwards [hS.mem_nhds hy] with w hw using hh w hw
    exact (((hfd.hasFDerivAt.const_mul a).add (hgd.hasFDerivAt.const_mul b)).congr_of_eventuallyEq hev).fderiv
  rw [e1.fderiv_eq]
  have hf1 : DifferentiableAt ℝ (fderiv ℝ f) z :=
    ((hfz z hz).fderiv_right (m := 1) (by first | norm_num | rfl | simp)).differentiableAt (by first | norm_num | simp)
  have hg1 : DifferentiableAt ℝ (fderiv ℝ g) z :=
    ((hgz z hz).fderiv_right (m := 1) (by first | norm_num | rfl | simp)).differentiableAt (by first | norm_num | simp)
  exact ((hf1.hasFDerivAt.const_smul a).add (hg1.hasFDerivAt.const_smul b)).fderiv

theorem isGood_interp {x : Ix κ → Ω} {m₀ m₁ : ConeMetric ℂ (Ix κ)} {μ : Measure (Ix κ → ℂ)}
    (hg₀ : IsGood D x m₀ μ) (hg₁ : IsGood D x m₁ μ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    IsGood D x (interp m₀ m₁ t) μ := by
  obtain ⟨ht0, ht1⟩ := ht
  have hS : IsOpen {z : Ix κ → ℂ | z ≠ 0} := isOpen_ne
  have hsm0 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) m₀.ρ {z | z ≠ 0} := hg₀.semipos.1
  have hsm1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) m₁.ρ {z | z ≠ 0} := hg₁.semipos.1
  have h2 : (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    first
      | exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤)
      | exact WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)
      | (norm_cast; exact le_top)
      | decide
  have hl0 : ContDiffOn ℝ 2 (fun z => Real.log (m₀.ρ z)) {z | z ≠ 0} :=
    (hsm0.of_le h2).log fun z hz => (m₀.pos z hz).ne'
  have hl1 : ContDiffOn ℝ 2 (fun z => Real.log (m₁.ρ z)) {z | z ≠ 0} :=
    (hsm1.of_le h2).log fun z hz => (m₁.pos z hz).ne'
  refine ⟨hg₀.arith, hg₀.indep, hg₀.smooth, ?_, ?_, hg₀.conjMu, hg₀.vol⟩
  · unfold IsSemipositiveOn
    refine ⟨?_, ?_⟩
    · show ContDiffOn ℝ _ (fun z => m₀.ρ z ^ (1 - t) * m₁.ρ z ^ t) _
      exact (hsm0.rpow_const_of_ne fun z hz => (m₀.pos z hz).ne').mul
        (hsm1.rpow_const_of_ne fun z hz => (m₁.pos z hz).ne')
    · intro z hz hz0 w hw
      have h0 := hg₀.semipos.2 z hz hz0 w hw
      have h1 := hg₁.semipos.2 z hz hz0 w hw
      unfold leviForm at h0 h1 ⊢
      rw [fderiv2_lin_comb (h := fun z => Real.log ((interp m₀ m₁ t).ρ z)) hS (1 - t) t hl0 hl1
        (fun y hy => by
          try dsimp only
          rw [interp_rho, Real.log_mul (Real.rpow_pos_of_pos (m₀.pos y hy) _).ne'
            (Real.rpow_pos_of_pos (m₁.pos y hy) _).ne', Real.log_rpow (m₀.pos y hy),
            Real.log_rpow (m₁.pos y hy)]) hz0]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
      nlinarith [mul_nonneg (sub_nonneg.mpr ht1) h0, mul_nonneg ht0 h1]
  · intro z
    rw [interp_rho, interp_rho, hg₀.conjM z, hg₁.conjM z]

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
