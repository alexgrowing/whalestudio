import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.MultivariableReproducingFormula

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal ComplexConjugate

namespace UpperTheory.Esk.ReproducingKernelExpansion

open UpperTheory.Esk

variable {F I Gf : Type} [Field F] [Group Gf] (D : Dat F I Gf)

theorem rep_eq (ω : D.Om) (u : Gf) (hu : (u : Gf ⧸ D.H) = ω) : ∃ h : D.H, D.rep ω = u * h := by
  have h1 : ((D.rep ω : Gf) : Gf ⧸ D.H) = ω := QuotientGroup.out_eq' _
  refine ⟨⟨u⁻¹ * D.rep ω, QuotientGroup.eq.1 (hu.trans h1.symm)⟩, ?_⟩
  simp

theorem ee_mul (h : D.H) (u : Gf) : D.ee ((h : Gf)⁻¹ * u) * (D.χ h : ℂ) = D.ee u := by
  unfold Dat.ee
  by_cases hu : u ∈ D.H
  · have hu' : (h : Gf)⁻¹ * u ∈ D.H := D.H.mul_mem (D.H.inv_mem h.2) hu
    rw [dif_pos hu', dif_pos hu, mul_comm, ← Units.val_mul, ← map_mul]
    congr 2
    apply Subtype.ext
    simp
  · have hu' : (h : Gf)⁻¹ * u ∉ D.H := fun hh => hu (by simpa using D.H.mul_mem h.2 hh)
    rw [dif_neg hu', dif_neg hu, zero_mul]

theorem ee_one : D.ee 1 = 1 := by
  unfold Dat.ee
  rw [dif_pos D.H.one_mem]
  exact congrArg Units.val (map_one D.χ)

theorem smul_fst (γ : PG F) (ω : D.Om) : γ • ω = (((D.j γ.out * D.rep ω : Gf)) : Gf ⧸ D.H) := by
  have h2 : ((D.rep ω : Gf) : Gf ⧸ D.H) = ω := QuotientGroup.out_eq' _
  conv_lhs => rw [← QuotientGroup.out_eq' γ, ← h2]
  exact D.mk_smulO γ.out (D.rep ω)

theorem smul_snd (γ : PG F) (w : D.Xs) : γ • w = D.act γ.out w := by
  conv_lhs => rw [← QuotientGroup.out_eq' γ]
  exact D.mk_smulX γ.out w

variable [Fintype I]

theorem term (k : I → ℕ) (f : X I × Gf → ℂ) (hf : D.IsForm k f) (z : X I) (x : Gf) (γ : PG F) (y : D.Y) :
    D.ee ((D.rep (γ • y).1)⁻¹ * x) * (qq k z (γ • y).2 * f ((γ • y).2, D.rep (γ • y).1)) =
      D.ee ((D.rep y.1)⁻¹ * (D.j γ.out)⁻¹ * x) * (qq k z (D.act γ.out y.2) * D.J k γ.out y.2) * f (y.2, D.rep y.1) := by
  obtain ⟨h, hh⟩ := rep_eq D (γ • y).1 (D.j γ.out * D.rep y.1) (by rw [Prod.smul_fst, smul_fst])
  have hs2 : (γ • y).2 = D.act γ.out y.2 := by rw [Prod.smul_snd, smul_snd]
  have key : (D.j γ.out * D.rep y.1 * (h : Gf))⁻¹ * x = (h : Gf)⁻¹ * ((D.rep y.1)⁻¹ * (D.j γ.out)⁻¹ * x) := by
    group
  rw [hh, hs2, hf.lev, show f (D.act γ.out y.2, D.j γ.out * D.rep y.1) = D.J k γ.out y.2 * f (y.2, D.rep y.1) from hf.aut _ _ _, key, ← ee_mul D h ((D.rep y.1)⁻¹ * (D.j γ.out)⁻¹ * x)]
  ring

open Classical in
theorem supp (k : I → ℕ) (f : X I × Gf → ℂ) (hf : D.IsForm k f) (z : X I) (x : Gf) (y : D.Y) :
    D.ee ((D.rep y.1)⁻¹ * x) * (qq k z y.2 * f (y.2, D.rep y.1)) =
      if y.1 = ((x : Gf) : Gf ⧸ D.H) then qq k z y.2 * f (y.2, x) else 0 := by
  split_ifs with hy
  · obtain ⟨h, hh⟩ := rep_eq D y.1 x hy.symm
    have he := ee_mul D h 1
    rw [ee_one, mul_one] at he
    have key : (x * (h : Gf))⁻¹ * x = (h : Gf)⁻¹ := by group
    rw [hh, show f (y.2, x * (h : Gf)) = (D.χ h : ℂ) * f (y.2, x) from hf.lev _ _ _, key]
    calc _ = (D.ee ((h : Gf)⁻¹) * (D.χ h : ℂ)) * (qq k z y.2 * f (y.2, x)) := by ring
      _ = _ := by rw [he, one_mul]
  · have hn : (D.rep y.1)⁻¹ * x ∉ D.H := by
      intro hm
      apply hy
      have h1 : ((D.rep y.1 : Gf) : Gf ⧸ D.H) = y.1 := QuotientGroup.out_eq' _
      exact h1.symm.trans (QuotientGroup.eq.2 hm)
    have h0 : D.ee ((D.rep y.1)⁻¹ * x) = 0 := by
      unfold Dat.ee
      rw [dif_neg hn]
    rw [h0, zero_mul]

end UpperTheory.Esk.ReproducingKernelExpansion

open UpperTheory.Esk UpperTheory.Esk.ReproducingKernelExpansion in
theorem UpperTheory.Esk.e5_of_reproducing_formula : UpperTheory.Esk.B1b → UpperTheory.Esk.C3 → UpperTheory.Esk.E0a → UpperTheory.Esk.faceMap_zero_comp_eq_one → UpperTheory.Esk.MultivariableReproducingFormula → UpperTheory.Esk.E5 := by
  intro hB1 hC3 hE0 _hE4 hB3 F I Gf _ _ _ D hAx k hk _hcomp b hb f hf p
  obtain ⟨z, x⟩ := p
  obtain ⟨hcount, hsf, -, hpres, -, -, hborel, -⟩ := hE0 F I Gf D hAx
  have := hcount
  have := hsf
  have := hborel
  have := hAx.cO
  let ω₀ : D.Om := ((x : Gf) : Gf ⧸ D.H)
  let a : D.Om → ℂ := ({ω₀} : Set D.Om).indicator fun _ => (1 : ℂ)
  let h0 : D.Xs → ℂ := fun w => qq k z w * f (w, x)
  let G : D.Y → ℂ := fun y => D.ee ((D.rep y.1)⁻¹ * x) * (qq k z y.2 * f (y.2, D.rep y.1))
  have hG : G = fun y => a y.1 * h0 y.2 := by
    funext y
    change D.ee ((D.rep y.1)⁻¹ * x) * (qq k z y.2 * f (y.2, D.rep y.1)) = a y.1 * h0 y.2
    rw [supp D k f hf z x y]
    by_cases hy : y.1 = ((x : Gf) : Gf ⧸ D.H)
    · rw [if_pos hy]
      have ha : a y.1 = 1 := by
        classical
        simp only [a]
        rw [Set.indicator_apply, if_pos (show y.1 ∈ ({ω₀} : Set D.Om) from hy)]
      rw [ha, one_mul]
    · rw [if_neg hy]
      have ha : a y.1 = 0 := by
        classical
        simp only [a]
        rw [Set.indicator_apply, if_neg (show y.1 ∉ ({ω₀} : Set D.Om) from hy)]
      rw [ha, zero_mul]
  have hqc : Continuous fun w : X I => qq k z w := by
    unfold qq
    exact continuous_finsetProd _ fun v _ =>
      (hB1.2.2.2.2.2.2.2.1 (k v)).comp (continuous_const.prodMk (continuous_apply v))
  have hh0c : Continuous fun w : X I => qq k z w * f (w, x) := hqc.mul (hf.hol x).1
  have hh0m : Measurable h0 := hh0c.measurable
  obtain ⟨C, hC⟩ := hf.bdd
  have hB := hB3 I k hk (fun w => f (w, x)) (hf.hol x) ⟨C, fun w => hC w x⟩ z
  have hh0i : Integrable h0 := hB.1
  have ham : Measurable a := measurable_const.indicator (MeasurableSet.of_discrete)
  have hai : Integrable a Measure.count :=
    (integrable_indicator_iff (MeasurableSet.of_discrete)).2
      ((integrableOn_singleton_iff (by simp)).2 (Or.inr (by simp)))
  have ha1 : ∫ ω, a ω ∂Measure.count = 1 := by
    simp only [a]
    rw [integral_indicator (MeasurableSet.of_discrete)]
    simp
  have hGm : Measurable G := by
    rw [hG]
    exact (ham.comp measurable_fst).mul (hh0m.comp measurable_snd)
  have hGi : Integrable G D.μY := by
    rw [hG]
    unfold Dat.μY
    exact MeasureTheory.Integrable.mul_prod hai hh0i
  have hKf : ∀ y : D.Y, D.Kern k y (z, x) * f (y.2, D.rep y.1) = ∑' γ : PG F, G (γ • y) := by
    intro y
    unfold Dat.Kern
    rw [← tsum_mul_right]
    refine tsum_congr fun γ => ?_
    exact (term D k f hf z x γ y).symm
  have hCC := hC3 (PG F) D.Y D.μY hpres b hb G hGm hGi
  calc ∫ y, b y • (D.Kern k y (z, x) * f (y.2, D.rep y.1)) ∂D.μY
      = ∫ y, b y • ∑' γ : PG F, G (γ • y) ∂D.μY := by simp_rw [hKf]
    _ = ∫ y, G y ∂D.μY := hCC.2
    _ = ∫ y, a y.1 * h0 y.2 ∂(Measure.count.prod volume) := by rw [hG]; rfl
    _ = (∫ ω, a ω ∂Measure.count) * ∫ w, h0 w := integral_prod_mul _ _
    _ = f (z, x) := by rw [ha1, one_mul]; exact hB.2
