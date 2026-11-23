import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialPullbackStatement
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LintegralImageEqLintegralNormSqDetMul
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscSt
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscPos

namespace ReciprocityTheory.AnForm.M

open MeasureTheory FinHolAtlas
open scoped ContDiff ComplexOrder Matrix

noncomputable section

def HessCGermStatement : Prop :=
  ∀ {D : ℕ} (φ ψ : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ), φ =ᶠ[nhds z] ψ → hessC φ z = hessC ψ z

theorem hessCGerm : HessCGermStatement := by
  intro D φ ψ z h
  have hH : fderiv ℝ (fderiv ℝ φ) z = fderiv ℝ (fderiv ℝ ψ) z := (h.fderiv (𝕜 := ℝ)).fderiv_eq
  show hessC φ z = hessC ψ z
  unfold hessC
  rw [hH]

theorem maDens_congr_hessC {D : ℕ} (φ ψ : Fin D → (Fin D → ℂ) → ℝ) (z : Fin D → ℂ)
    (h : ∀ k, hessC (φ k) z = hessC (ψ k) z) : maDens φ z = maDens ψ z := by
  simp only [maDens, h]

theorem potSmoothAt {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (P : LocPot X)
    (hP : IsPotential A P) (x : X) (j : Fin A.n) {y : Fin e → ℂ}
    (hy : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' P.U x) :
    ContDiffAt ℝ 2 (P.φ x ∘ (A.chart j).symm) y := by
  have hopen : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' P.U x) :=
    (A.chart j).isOpen_inter_preimage_symm (P.isOpen_U x)
  exact ((hP.1 x j).contDiffAt (hopen.mem_nhds hy)).of_le (by first | exact ENat.LEInfty.out | simp | norm_num)

theorem potSmoothOn {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (P : LocPot X)
    (hP : IsPotential A P) (x : X) (j : Fin A.n) :
    ContDiffOn ℝ 2 (P.φ x ∘ (A.chart j).symm) ((A.chart j).target ∩ (A.chart j).symm ⁻¹' P.U x) := by
  exact (hP.1 x j).of_le (by first | exact ENat.LEInfty.out | simp | norm_num)

theorem locDensBase : LocDensBaseStatement := by
  intro e X _ A Φ hΦ j y hy x hx
  unfold locDens
  apply maDens_congr_hessC
  intro i
  obtain ⟨W, hW, hpW, G, hG, hGeq⟩ :=
    (hΦ i).2 ((A.chart j).symm y) (x i) ((A.chart j).symm y) ⟨(Φ i).mem_U _, hx i⟩

  have hopen : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹'
      (W ∩ (Φ i).U ((A.chart j).symm y) ∩ (Φ i).U (x i))) :=
    (A.chart j).isOpen_inter_preimage_symm
      ((hW.inter ((Φ i).isOpen_U _)).inter ((Φ i).isOpen_U (x i)))
  have hmem : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹'
      (W ∩ (Φ i).U ((A.chart j).symm y) ∩ (Φ i).U (x i)) :=
    ⟨hy, ⟨⟨hpW, (Φ i).mem_U _⟩, hx i⟩⟩
  have hev : (fun y' => (Φ i).φ ((A.chart j).symm y) ((A.chart j).symm y')) =ᶠ[nhds y]
      (fun y' => (Φ i).φ (x i) ((A.chart j).symm y') + (G ((A.chart j).symm y')).re) := by
    filter_upwards [hopen.mem_nhds hmem] with y' hy'
    rw [← hGeq _ hy'.2]
    ring
  have hGa : AnalyticAt ℂ (G ∘ (A.chart j).symm) y := hG j y ⟨hy, hpW⟩
  have hφs : ContDiffAt ℝ 2 ((Φ i).φ (x i) ∘ (A.chart j).symm) y :=
    potSmoothAt A (Φ i) (hΦ i) (x i) j ⟨hy, hx i⟩
  exact (hessCGerm _ _ y hev).trans (ReciprocityTheory.AnForm.A.hessC_add_re_analytic _ (G ∘ (A.chart j).symm) y hφs hGa)

theorem hessC_continuousOn {D : ℕ} (ψ : (Fin D → ℂ) → ℝ) (V : Set (Fin D → ℂ)) (hV : IsOpen V)
    (hψ : ContDiffOn ℝ 2 ψ V) : ContinuousOn (hessC ψ) V := by
  have h1 : ContDiffOn ℝ 1 (fun y => fderiv ℝ ψ y) V := hψ.fderiv_of_isOpen hV (by norm_num)
  have h2 : ContinuousOn (fun y => fderiv ℝ (fderiv ℝ ψ) y) V :=
    h1.continuousOn_fderiv_of_isOpen hV le_rfl

  have ev : ∀ a b : Fin D → ℂ, ContinuousOn (fun y => fderiv ℝ (fderiv ℝ ψ) y a b) V :=
    fun a b => (h2.clm_apply continuousOn_const).clm_apply continuousOn_const
  refine continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => ?_
  unfold hessC
  dsimp only
  have hre := Complex.continuous_ofReal.comp_continuousOn
    ((ev (Pi.single i 1) (Pi.single j 1)).add
      (ev (Complex.I • Pi.single i 1) (Complex.I • Pi.single j 1)))
  have him := Complex.continuous_ofReal.comp_continuousOn
    ((ev (Pi.single i 1) (Complex.I • Pi.single j 1)).sub
      (ev (Complex.I • Pi.single i 1) (Pi.single j 1)))
  exact (hre.add (continuousOn_const.mul him)).div_const 4

theorem maDens_continuousOn {D : ℕ} (φ : Fin D → (Fin D → ℂ) → ℝ) (V : Set (Fin D → ℂ))
    (hV : IsOpen V) (hφ : ∀ k, ContDiffOn ℝ 2 (φ k) V) : ContinuousOn (maDens φ) V := by
  have hH : ∀ k, ContinuousOn (hessC (φ k)) V := fun k => hessC_continuousOn (φ k) V hV (hφ k)
  unfold maDens mdisc
  refine continuousOn_const.mul (Complex.continuous_re.comp_continuousOn ?_)
  refine continuousOn_const.mul (continuousOn_finset_sum _ fun S _ => continuousOn_const.mul ?_)
  exact (continuous_id.matrix_det).comp_continuousOn (continuousOn_finset_sum _ fun k _ => hH k)

theorem locDensCont : LocDensContStatement := by
  intro e X _ A Φ hΦ j y0 hy0

  let x : Fin e → X := fun _ => (A.chart j).symm y0
  let V := (A.chart j).target ∩ (A.chart j).symm ⁻¹' ⋂ i, (Φ i).U (x i)
  have hV : IsOpen V :=
    (A.chart j).isOpen_inter_preimage_symm (isOpen_iInter_of_finite fun i => (Φ i).isOpen_U (x i))
  have hy0V : y0 ∈ V := ⟨hy0, Set.mem_iInter.2 fun i => (Φ i).mem_U _⟩
  have hsm : ∀ i, ContDiffOn ℝ 2 (fun y' => (Φ i).φ (x i) ((A.chart j).symm y')) V := fun i =>
    (potSmoothOn A (Φ i) (hΦ i) (x i) j).mono fun y hy => ⟨hy.1, Set.mem_iInter.1 hy.2 i⟩
  have hg := (maDens_continuousOn _ V hV hsm).continuousAt (hV.mem_nhds hy0V)
  have hev : (maDens fun i y' => (Φ i).φ (x i) ((A.chart j).symm y')) =ᶠ[nhds y0]
      locDens A Φ j := by
    filter_upwards [hV.mem_nhds hy0V] with y hy
    exact (locDensBase A Φ hΦ j y hy.1 x fun i => Set.mem_iInter.1 hy.2 i).symm
  exact (hg.congr hev).continuousWithinAt

theorem locDensChart : LocDensChartStatement := by
  intro e X _ A Φ hΦ j k y hy hyk
  have hback : (A.chart k).symm (A.chart k ((A.chart j).symm y)) = (A.chart j).symm y :=
    (A.chart k).left_inv hyk
  have hτa : AnalyticAt ℂ (A.chart k ∘ (A.chart j).symm) y := A.holo j k y ⟨hy, hyk⟩
  have hO : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart k).source) :=
    (A.chart j).isOpen_inter_preimage_symm (A.chart k).open_source
  have hsm : ∀ i, ContDiffAt ℝ 2 ((Φ i).φ ((A.chart j).symm y) ∘ (A.chart k).symm)
      ((A.chart k ∘ (A.chart j).symm) y) := fun i =>
    potSmoothAt A (Φ i) (hΦ i) _ k ⟨(A.chart k).map_source hyk, by
      simp only [Set.mem_preimage, Function.comp_apply, hback]; exact (Φ i).mem_U _⟩
  have hcomp := ReciprocityTheory.AnForm.A.maDens_comp (fun i => (Φ i).φ ((A.chart j).symm y) ∘ (A.chart k).symm)
    (A.chart k ∘ (A.chart j).symm) y hτa hsm

  have hL : locDens A Φ j y = maDens (fun i => ((Φ i).φ ((A.chart j).symm y) ∘ (A.chart k).symm) ∘
      (A.chart k ∘ (A.chart j).symm)) y := by
    unfold locDens
    apply maDens_congr_hessC
    intro i
    refine hessCGerm _ _ _ ?_
    filter_upwards [hO.mem_nhds ⟨hy, hyk⟩] with y' hy'
    simp only [Function.comp_apply, (A.chart k).left_inv hy'.2]
  rw [hL, hcomp, ReciprocityTheory.AnForm.A.det_jacC, Complex.normSq_eq_norm_sq]
  unfold locDens
  simp only [Function.comp_apply, hback]
  rfl

theorem re_star_dot_hessC {D : ℕ} (φ : (Fin D → ℂ) → ℝ) (z x : Fin D → ℂ) :
    (star x ⬝ᵥ (hessC φ z *ᵥ x)).re = levi φ z (star x) := by
  classical
  obtain ⟨H, hH⟩ : ∃ H, H = fderiv ℝ (fderiv ℝ φ) z := ⟨_, rfl⟩
  let E : Fin D → Fin D → ℂ := fun i => Pi.single i 1

  have hw : star x = ∑ i, ((x i).re • E i + (-(x i).im) • (Complex.I • E i)) := by
    ext k
    rw [Finset.sum_apply, Finset.sum_eq_single k
      (fun i _ hik => by simp [E, Pi.single_apply, hik.symm]) (by simp)]
    simp [E, Complex.ext_iff]
  have hIw : Complex.I • star x = ∑ i, ((x i).im • E i + (x i).re • (Complex.I • E i)) := by
    ext k
    rw [Finset.sum_apply, Finset.sum_eq_single k
      (fun i _ hik => by simp [E, Pi.single_apply, hik.symm]) (by simp)]
    simp [E, Complex.ext_iff]
  have hL : (star x ⬝ᵥ (hessC φ z *ᵥ x)).re = ∑ i, ∑ j,
      (((x i).re * (x j).re + (x i).im * (x j).im) *
          (H (E i) (E j) + H (Complex.I • E i) (Complex.I • E j)) +
        ((x i).im * (x j).re - (x i).re * (x j).im) *
          (H (E i) (Complex.I • E j) - H (Complex.I • E i) (E j))) / 4 := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [ReciprocityTheory.AnForm.A.TraceConjugationCover.hessC_eq_lv, ← hH]
    simp [ReciprocityTheory.AnForm.A.TraceConjugationCover.lv, E, Complex.mul_re, Complex.mul_im]
    ring
  have hR : levi φ z (star x) = ∑ i, ∑ j,
      (((x i).re * (x j).re + (x i).im * (x j).im) *
          (H (E i) (E j) + H (Complex.I • E i) (Complex.I • E j)) +
        ((x i).im * (x j).re - (x i).re * (x j).im) *
          (H (E i) (Complex.I • E j) - H (Complex.I • E i) (E j))) / 4 := by
    unfold levi
    rw [← hH, hIw, hw]
    simp only [map_sum, map_add, map_smul, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_smul',
      Pi.smul_apply, smul_eq_mul]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hL, hR]

theorem hessC_posDef {D : ℕ} (φ : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) (hφ : ContDiffAt ℝ 2 φ z)
    (hpos : ∀ w : Fin D → ℂ, w ≠ 0 → 0 < levi φ z w) : (hessC φ z).PosDef := by
  have hH := ReciprocityTheory.AnForm.A.hessC_isHermitian φ z hφ
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hH fun x hx => ?_
  have hw : star x ≠ 0 := star_ne_zero.2 hx
  have him := hH.im_star_dotProduct_mulVec_self x
  rw [Complex.lt_def]
  refine ⟨?_, ?_⟩
  · rw [Complex.zero_re, re_star_dot_hessC]
    exact hpos _ hw
  · rw [Complex.zero_im]
    exact him.symm

theorem locDensPos : LocDensPosStatement := by
  intro e X _ A Φ hΦ hpos j y hy
  have hPD : ∀ i, (hessC (fun y' => (Φ i).φ ((A.chart j).symm y) ((A.chart j).symm y')) y).PosDef :=
    fun i => hessC_posDef _ y (potSmoothAt A (Φ i) (hΦ i) _ j ⟨hy, (Φ i).mem_U _⟩)
      (fun w hw => hpos i _ j y ⟨hy, (Φ i).mem_U _⟩ w hw)
  have hm := (ReciprocityTheory.AnForm.A.mdisc_pos_of_posDef
    (fun i => hessC (fun y' => (Φ i).φ ((A.chart j).symm y) ((A.chart j).symm y')) y) hPD).2
  have hpi : 0 < (2 / Real.pi) := div_pos two_pos Real.pi_pos
  have hf : (0 : ℝ) < (e.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos e
  exact mul_pos (mul_pos hf (pow_pos hpi e)) hm

end

end ReciprocityTheory.AnForm.M
