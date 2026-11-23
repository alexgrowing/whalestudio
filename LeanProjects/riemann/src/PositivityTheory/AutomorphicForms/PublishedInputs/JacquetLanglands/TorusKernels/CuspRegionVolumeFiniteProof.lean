import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.MultivariableReproducingFormula

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal ComplexConjugate

namespace UpperTheory.Esk.CuspRegionVolume

open UpperTheory.Esk

def B1 (C c : ℝ) : Set {z : ℂ // z.im ≠ 0} := {w | |w.1.re| ≤ C ∧ c ≤ |w.1.im|}

theorem measurableSet_cusp_region (C c : ℝ) : MeasurableSet (B1 C c) := by
  have h1 : Measurable fun w : {z : ℂ // z.im ≠ 0} => |w.1.re| :=
    (continuous_abs.comp (Complex.continuous_re.comp continuous_subtype_val)).measurable
  have h2 : Measurable fun w : {z : ℂ // z.im ≠ 0} => |w.1.im| :=
    (continuous_abs.comp (Complex.continuous_im.comp continuous_subtype_val)).measurable
  exact (measurableSet_le h1 measurable_const).inter (measurableSet_le measurable_const h2)

theorem pt_bound (C c : ℝ) (hc : 0 < c) (t : ℂ) (h1 : |t.re| ≤ C) (h2 : c ≤ |t.im|) :
    1 / t.im ^ 2 ≤ (1 + C ^ 2) * (1 + 1 / c ^ 2) * ((1 + t.re ^ 2)⁻¹ * (1 + t.im ^ 2)⁻¹) := by
  have hc2 : 0 < c ^ 2 := by positivity
  have hb : c ^ 2 ≤ t.im ^ 2 := by
    nlinarith [sq_abs t.im, mul_nonneg (sub_nonneg.2 h2) (add_nonneg (abs_nonneg t.im) hc.le)]
  have ha : t.re ^ 2 ≤ C ^ 2 := by
    nlinarith [sq_abs t.re, mul_nonneg (sub_nonneg.2 h1) (by linarith [abs_nonneg t.re] : 0 ≤ C + |t.re|)]
  have hbpos : 0 < t.im ^ 2 := lt_of_lt_of_le hc2 hb
  have e1 : 1 ≤ (1 + C ^ 2) * (1 + t.re ^ 2)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    linarith
  have e2 : 1 / t.im ^ 2 ≤ (1 + 1 / c ^ 2) * (1 + t.im ^ 2)⁻¹ := by
    have h3 : 1 ≤ t.im ^ 2 / c ^ 2 := by
      rw [le_div_iff₀ hc2]
      linarith
    rw [← div_eq_mul_inv, div_le_div_iff₀ hbpos (by positivity), add_mul, one_mul, one_div, inv_mul_eq_div]
    linarith
  calc 1 / t.im ^ 2 = 1 * (1 / t.im ^ 2) := (one_mul _).symm
    _ ≤ ((1 + C ^ 2) * (1 + t.re ^ 2)⁻¹) * ((1 + 1 / c ^ 2) * (1 + t.im ^ 2)⁻¹) :=
        mul_le_mul e1 e2 (by positivity) (by positivity)
    _ = (1 + C ^ 2) * (1 + 1 / c ^ 2) * ((1 + t.re ^ 2)⁻¹ * (1 + t.im ^ 2)⁻¹) := by ring

theorem integ_G : ∫⁻ t : ℂ, ENNReal.ofReal ((1 + t.re ^ 2)⁻¹ * (1 + t.im ^ 2)⁻¹) < ⊤ := by
  have h1 : Integrable (fun x : ℝ => (1 + x ^ 2)⁻¹) := integrable_inv_one_add_sq
  have h2 : Integrable (fun p : ℝ × ℝ => (1 + p.1 ^ 2)⁻¹ * (1 + p.2 ^ 2)⁻¹) :=
    h1.mul_prod h1
  have h3 : Integrable (fun t : ℂ => (1 + t.re ^ 2)⁻¹ * (1 + t.im ^ 2)⁻¹) :=
    (Complex.volume_preserving_equiv_real_prod.integrable_comp h2.aestronglyMeasurable).2 h2
  exact h3.lintegral_lt_top

private theorem volume_eq_lintegral_inv_im_sq_comap (s : Set {z : ℂ // z.im ≠ 0}) (hs : MeasurableSet s) :
    (volume : Measure P) (show Set P from s) = ∫⁻ z in s, ENNReal.ofReal (1 / z.1.im ^ 2)
      ∂(Measure.comap (Subtype.val : {z : ℂ // z.im ≠ 0} → ℂ) volume) :=
  withDensity_apply _ hs

private theorem lintegral_comap_im_ne_zero_le_lintegral (f : ℂ → ℝ≥0∞) :
    ∫⁻ z : {z : ℂ // z.im ≠ 0}, f z.1 ∂(Measure.comap Subtype.val volume) ≤ ∫⁻ t, f t := by
  have hs : MeasurableSet {z : ℂ | z.im ≠ 0} :=
    (isOpen_ne_fun Complex.continuous_im continuous_const).measurableSet
  calc ∫⁻ z : {z : ℂ // z.im ≠ 0}, f z.1 ∂(Measure.comap Subtype.val volume)
      = ∫⁻ t in {z : ℂ | z.im ≠ 0}, f t := lintegral_subtype_comap hs f
    _ ≤ ∫⁻ t, f t := setLIntegral_le_lintegral _ _

private theorem lintegral_mul_inv_one_add_sq_lt_top (K : ℝ) (hK : 0 ≤ K) :
    ∫⁻ t : ℂ, ENNReal.ofReal (K * ((1 + t.re ^ 2)⁻¹ * (1 + t.im ^ 2)⁻¹)) < ⊤ := by
  simp_rw [ENNReal.ofReal_mul hK]
  rw [lintegral_const_mul _ (by fun_prop)]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top integ_G

private theorem lintegral_B1_inv_im_sq_le_lintegral (C c : ℝ) (hc : 0 < c) :
    ∫⁻ z in B1 C c, ENNReal.ofReal (1 / z.1.im ^ 2) ∂(Measure.comap Subtype.val volume) ≤
      ∫⁻ z : {z : ℂ // z.im ≠ 0}, ENNReal.ofReal ((1 + C ^ 2) * (1 + 1 / c ^ 2) *
          ((1 + z.1.re ^ 2)⁻¹ * (1 + z.1.im ^ 2)⁻¹)) ∂(Measure.comap Subtype.val volume) := by
  refine le_trans (setLIntegral_mono' (measurableSet_cusp_region C c) fun z hz => ?_) (setLIntegral_le_lintegral _ _)
  exact ENNReal.ofReal_le_ofReal (pt_bound C c hc z.1 hz.1 hz.2)

theorem volume_cusp_region_lt_top (C c : ℝ) (hc : 0 < c) : (volume : Measure P) (show Set P from B1 C c) < ⊤ := by
  have hK0 : 0 ≤ (1 + C ^ 2) * (1 + 1 / c ^ 2) := by positivity
  rw [volume_eq_lintegral_inv_im_sq_comap _ (measurableSet_cusp_region C c)]
  exact lt_of_le_of_lt ((lintegral_B1_inv_im_sq_le_lintegral C c hc).trans (lintegral_comap_im_ne_zero_le_lintegral _)) (lintegral_mul_inv_one_add_sq_lt_top _ hK0)

end UpperTheory.Esk.CuspRegionVolume

open UpperTheory.Esk.CuspRegionVolume in
theorem UpperTheory.Esk.cusp_region_volume_finite_proof : UpperTheory.Esk.B1a → UpperTheory.Esk.UpperHalfPlaneMeasureCoordinates → UpperTheory.Esk.C2 → UpperTheory.Esk.E0a → UpperTheory.Esk.E0d → UpperTheory.Esk.E3 := by
  intro hB1a _ hC2 hE0a hE0d
  intro F I Gf _ _ _ D hD b hb
  obtain ⟨hcnt, hsf, -, hPY, -, -, -, -⟩ := hE0a F I Gf D hD
  obtain ⟨-, hsm, -, -, -, -, -, -, -, hsurj, -⟩ := hE0d F I Gf D hD
  haveI : Countable (PG F) := hcnt
  haveI : SigmaFinite (volume : Measure D.Xs) := hsf
  haveI : SigmaFinite (volume : Measure P) := hB1a.1
  haveI : Countable D.Om := hD.cO
  obtain ⟨c₀, hc₀, hmink⟩ := hD.mink
  obtain ⟨S, C, c, hc, hnorm⟩ := hD.normal c₀ hc₀
  have h01 : (![0, 1] : Fin 2 → F) ≠ 0 := fun h => by simpa using congrFun h 1
  let T : Set D.Om := (fun x : Gf => (show D.Om from ((x : Gf) : Gf ⧸ D.H))) '' (S : Set Gf)
  let U : Set D.Xs := Set.univ.pi fun _ : I => (show Set P from B1 C c)
  have hT : T.Finite := S.finite_toSet.image _
  have hU : MeasurableSet U := MeasurableSet.univ_pi fun _ => measurableSet_cusp_region C c
  have hS : MeasurableSet (T ×ˢ U) := (MeasurableSet.of_discrete).prod hU
  have hcover : ∀ y : D.Y, ∃ g : PG F, g • y ∈ T ×ˢ U := by
    intro y
    obtain ⟨s, hs0, hs⟩ := hmink y.2 (D.rep y.1)
    obtain ⟨γ, hγ⟩ := hsurj s hs0
    set y' : D.Y := (γ : PG F) • y with hy'
    have h1 : c₀ ≤ D.Ht ![0, 1] y'.2 (D.rep y'.1) := by
      change c₀ ≤ D.HtY ![0, 1] ((γ : PG F) • y)
      rw [hsm ![0, 1] h01 γ y, hγ]
      exact hs
    obtain ⟨bb, -, ⟨x', hx'S, h, hhH, hjx⟩, hSg⟩ := hnorm y'.2 (D.rep y'.1) h1
    refine ⟨(bb : PG F) * (γ : PG F), ?_⟩
    rw [mul_smul, ← hy']
    refine ⟨?_, ?_⟩
    · have hy1 : ((D.rep y'.1 : Gf) : Gf ⧸ D.H) = y'.1 := Quotient.out_eq _
      have hm := D.mk_smulO bb (D.rep y'.1)
      rw [hy1] at hm
      refine ⟨x', hx'S, ?_⟩
      show (show D.Om from ((x' : Gf) : Gf ⧸ D.H)) = (bb : PG F) • y'.1
      rw [hm, hjx]
      refine (QuotientGroup.eq.2 ?_).symm
      rw [_root_.mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
      exact inv_mem hhH
    · show (bb : PG F) • y'.2 ∈ U
      rw [D.mk_smulX]
      intro v _
      exact ⟨(hSg v).1, (hSg v).2.1⟩
  have hfin : D.μY (T ×ˢ U) < ⊤ := by
    unfold Dat.μY
    rw [Measure.prod_prod]
    refine ENNReal.mul_lt_top (Measure.count_apply_lt_top.2 hT) ?_
    change (Measure.pi fun _ : I => (volume : Measure P)) (Set.univ.pi fun _ : I => (show Set P from B1 C c)) < ⊤
    rw [Measure.pi_pi]
    exact ENNReal.prod_lt_top fun _ _ => volume_cusp_region_lt_top C c hc
  exact lt_of_le_of_lt ((hC2 (PG F) D.Y).2 D.μY hPY b hb _ hS hcover) hfin
