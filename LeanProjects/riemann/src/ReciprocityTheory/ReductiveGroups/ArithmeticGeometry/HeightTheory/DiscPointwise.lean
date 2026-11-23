import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HDiscBDefs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.TraceFib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.AeEvTNeZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.TraceGramDetNeZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HadamardGram
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HNormPts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.GeneratorNeZeroOfHeight

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem disc_pointwise (hd : d.AxH 𝒜) (h : d.S1) (a b : KTp K d.D d.N) (hab : d.IsPres hd h a b)
    (sg : K →+* ℂ) :
    ∀ᵐ z ∂(ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1)),
      Real.log ‖d.evT sg 0 (d.tOf z) a‖ - Real.log ‖d.evT sg 0 (d.tOf z) b‖ ≤
        d.del * Real.log d.del + 2 * ∑ k, Real.log (d.supN sg d.wF (d.thp (hd.sel k))) +
          2 * ∑ c, ∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (d.tOf z)),
            -Real.log (d.nrm c d.wF (hd.a4.choose c) P) := by
  classical
  obtain ⟨hb0, habE, m, hm0, hma, hmb⟩ := hab
  have hDe := d.de_ne_zero hd h
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at habE
    exact mul_ne_zero hDe ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hb0) habE.symm
  have heW : ∀ c, hd.a4.choose c ∈ 𝒜 c d.wF ∧ hd.a4.choose c ≠ 0 := hd.a4.choose_spec.1
  have hST := MeasureTheory.ae_all_iff.mpr fun c => d.norm_at_sg hd h c sg
  filter_upwards [hST, d.de_fibre hd h a b ⟨hb0, habE, m, hm0, hma, hmb⟩ sg,
    d.ae_evT_ne_zero sg a ha0 m hm0 hma, d.ae_evT_ne_zero sg b hb0 m hm0 hmb] with z hz hfib haz hbz
  set e := hd.a4.choose with he
  set t := d.tOf z with ht
  set s : Fin d.del → ℝ := fun k => d.supN sg d.wF (d.thp (hd.sel k)) with hsdef
  have hfin : ∀ c, (d.ST c sg t).Finite := fun c => (hz c).1
  have hcard : ∀ c, (d.ST c sg t).ncard = d.delc c := fun c => (hz c).2.1
  let _ : ∀ c, Fintype (d.ST c sg t) := fun c => (hfin c).fintype
  let M : (Σ c, d.ST c sg t) → Fin d.del → ℂ := fun r k =>
    (r.2 : Ω r.1 →+* ℂ) (ratio (Ω := Ω r.1) (d.thp (hd.sel k) r.1) (e r.1))
  let ν : (Σ c, d.ST c sg t) → ℝ := fun r => d.nrm r.1 d.wF (e r.1) r.2
  have hR : Fintype.card (Σ c, d.ST c sg t) = d.del := by
    rw [Fintype.card_sigma]
    unfold Data.del
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← hcard c, ← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  have hν : ∀ r, 0 < ν r := fun r => hd.nrm_pos r.1 r.2 (heW r.1).1 (heW r.1).2
  have hM : ∀ r k, ‖M r k‖ * ν r ≤ s k := by
    rintro ⟨c, P, hP⟩ k
    have hth : d.thp (hd.sel k) c ∈ 𝒜 c d.wF := hd.thp_mem _ c
    have hline := eq_ratio_smul_on_line d (hd := hd) hth (heW c).1 (heW c).2
    have h1 : ‖P (ratio (Ω := Ω c) (d.thp (hd.sel k) c) (e c))‖ * d.nrm c d.wF (e c) P ≤
        d.nrm c d.wF (d.thp (hd.sel k) c) P := by
      by_cases hr : ratio (Ω := Ω c) (d.thp (hd.sel k) c) (e c) = 0
      · rw [hr, map_zero, norm_zero, zero_mul]
        rw [hr, zero_smul] at hline
        rw [hline, hd.nrm_zero]
      · have h2 := hd.nrm_smul c P _ (heW c).1 (heW c).2 hr
        rw [← hline] at h2
        rw [h2]
    have hmem : d.thp (hd.sel k) ∈ d.Thp := by
      rw [hd.Thp_span]
      exact Submodule.subset_span ⟨_, rfl⟩
    have h3 : d.nrm c d.wF (d.thp (hd.sel k) c) P ≤ s k :=
      le_ciSup (f := fun p : (Σ c, PT (Ω := Ω c) sg) => d.nrm p.1 d.wF (d.thp (hd.sel k) p.1) p.2)
        (hd.bdd sg d.wF (d.thp (hd.sel k)) (Or.inr (Or.inl ⟨hmem, rfl⟩))) ⟨c, ⟨P, hP.1⟩⟩
    exact h1.trans h3
  have hG : (Matrix.of fun k l : Fin d.del => ∑ c, ∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg t),
        P (ratio (Ω := Ω c) (d.thp (hd.sel k) c) (e c)) *
          P (ratio (Ω := Ω c) (d.thp (hd.sel l) c) (e c))) =
      Matrix.of fun k l => ∑ r, M r k * M r l := by
    ext k l
    simp only [Matrix.of_apply, Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← finsum_set_coe_eq_finsum_mem, finsum_eq_sum_of_fintype]
  have hq : d.evT sg 0 t a / d.evT sg 0 t b = (Matrix.of fun k l : Fin d.del => ∑ r, M r k * M r l).det := by
    rw [hfib hbz, hG]
  set D0 := (Matrix.of fun k l : Fin d.del => ∑ r, M r k * M r l).det with hD0
  have hD0ne : D0 ≠ 0 := by
    rw [← hq]
    exact div_ne_zero haz hbz
  have hlhs : Real.log ‖d.evT sg 0 t a‖ - Real.log ‖d.evT sg 0 t b‖ = Real.log ‖D0‖ := by
    rw [← hq, norm_div, Real.log_div (norm_ne_zero_iff.mpr haz) (norm_ne_zero_iff.mpr hbz)]
  have hH := hadamard_gram hR M ν s hν hM
  have hpos : 0 < ‖D0‖ * ∏ r, ν r ^ 2 :=
    mul_pos (norm_pos_iff.mpr hD0ne) (Finset.prod_pos fun r _ => pow_pos (hν r) 2)
  have hRpos : 0 < (d.del : ℝ) ^ d.del * ∏ k, s k ^ 2 := lt_of_lt_of_le hpos hH
  have hlog := Real.log_le_log hpos hH
  have hs : ∀ k, s k ^ 2 ≠ 0 := fun k =>
    (Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul hRpos.ne')) k (Finset.mem_univ _)
  have hdel : (d.del : ℝ) ^ d.del ≠ 0 := left_ne_zero_of_mul hRpos.ne'
  rw [Real.log_mul (norm_ne_zero_iff.mpr hD0ne)
      (Finset.prod_ne_zero_iff.mpr fun r _ => pow_ne_zero 2 (hν r).ne'),
    Real.log_prod (fun r _ => pow_ne_zero 2 (hν r).ne'),
    Real.log_mul hdel (Finset.prod_ne_zero_iff.mpr fun k _ => hs k),
    Real.log_prod (fun k _ => hs k)] at hlog
  simp only [Real.log_pow, Nat.cast_ofNat] at hlog
  have hsumν : ∑ r, Real.log (ν r) = ∑ c, ∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg t),
      Real.log (d.nrm c d.wF (e c) P) := by
    rw [Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← finsum_set_coe_eq_finsum_mem, finsum_eq_sum_of_fintype]
  have hsumneg : ∑ c, ∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg t), -Real.log (d.nrm c d.wF (e c) P) =
      -∑ c, ∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg t), Real.log (d.nrm c d.wF (e c) P) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← finsum_set_coe_eq_finsum_mem, ← finsum_set_coe_eq_finsum_mem, finsum_eq_sum_of_fintype,
      finsum_eq_sum_of_fintype, Finset.sum_neg_distrib]
  rw [hlhs, hsumneg, ← hsumν]
  have e1 : ∑ r, (2 : ℝ) * Real.log (ν r) = 2 * ∑ r, Real.log (ν r) := by rw [Finset.mul_sum]
  have e2 : ∑ k, (2 : ℝ) * Real.log (s k) = 2 * ∑ k, Real.log (s k) := by rw [Finset.mul_sum]
  rw [e1, e2] at hlog
  linarith

end Data

end ReciprocityTheory.ChartRestriction.G.T0
