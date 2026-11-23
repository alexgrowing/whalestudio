import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Values
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Weights
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree.Line

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open scoped Matrix ComplexConjugate

variable (II : IntersectionSystem)
  (hII : ∀ W : Ideal (MRing (PBlk 2)), IsArithVar W 1 → 0 ≤ II Unit (PBlk 2) W 1 ![fsLine 2])

theorem mem_lineF_apply_one {v : Fin 2 → Ω} (hv : v ∈ lineF) : v 1 = 0 := by
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hv
  simp

theorem valAt_line_zero {z : (Σ _ : Unit, Fin 2) → ℂ} : valAt yLine (0 : Ω) z = 0 := by
  classical
  have h : IsValueAt yLine (0 : Ω) z 0 := by simpa using isValueAt_intCast yLine z 0
  unfold valAt
  rw [dif_pos ⟨0, h⟩]
  obtain ⟨d, g, h', hg, hh, hy, heq, hz0, hv⟩ := (⟨0, h⟩ : ∃ v, IsValueAt yLine (0 : Ω) z v).choose_spec
  rw [hv]
  rw [zero_mul] at heq
  have hg0 : g = 0 := by
    have := mem_mCoordIdeal_of_aeval_eq_zero yLine hg heq
    rwa [mCoordIdeal_yLine, Ideal.mem_bot] at this
  simp [hg0]

variable {II hII}

section Frame

variable {z : (Σ _ : Unit, Fin 2) → ℂ} (d : MuFrameAt (lineHodge II hII) z)

abbrev fb : Fin 2 → Fin 2 → Ω := d.b ()

theorem fb_zero_one : fb d 0 1 = 0 := by
  have h := (d.adapted ()).2.2
  have hmem : fb d 0 ∈ lineF := by
    change Submodule.span Ω (Set.range (d.b () ∘ headIdx (show 1 ≤ 2 by decide))) = lineF at h
    rw [← h]
    exact Submodule.subset_span ⟨0, rfl⟩
  exact mem_lineF_apply_one hmem

set_option maxHeartbeats 2000000 in
theorem u_mul_fb : d.u * fb d 1 1 = 1 := by
  have heq : (PiTensorProduct.tprod Ω (fun _ : Unit => exteriorPower.ιMulti Ω 1
      (fun a : Fin 1 => lineF.mkQ ((Pi.basisFun Ω (Fin 2)) (tailIdx (show 1 ≤ 2 by decide) a)))) :
        PiTensorProduct Ω (fun _ : Unit => ⋀[Ω]^1 ((Fin 2 → Ω) ⧸ lineF))) =
      (d.u * chartMono yLine d.c 0) • PiTensorProduct.tprod Ω (fun _ : Unit => exteriorPower.ιMulti Ω 1
        (fun a : Fin 1 => lineF.mkQ (d.b () (tailIdx (show 1 ≤ 2 by decide) a)))) := d.eq
  have e1 := congrArg (PiTensorProduct.subsingletonEquiv (R := Ω)
    (s := fun _ : Unit => ⋀[Ω]^1 ((Fin 2 → Ω) ⧸ lineF)) ()) heq
  rw [LinearEquiv.map_smul] at e1
  simp only [PiTensorProduct.subsingletonEquiv_apply_tprod] at e1
  have e2 := congrArg (exteriorPower.oneEquiv Ω ((Fin 2 → Ω) ⧸ lineF)) e1
  simp only [map_smul, exteriorPower.oneEquiv_ιMulti, chartMono, Finset.univ_unique,
    Finset.prod_singleton] at e2
  have ht' : ∀ (h : 1 ≤ 2) (a : Fin (2 - 1)), tailIdx h a = 1 := fun _ a => Fin.ext (by
    have := a.isLt
    simp only [tailIdx, Fin.val_one]
    omega)
  simp only [ht', Pi.basisFun_apply, Pi.zero_apply, zpow_zero, mul_one, Submodule.mkQ_apply,
    ← Submodule.Quotient.mk_smul] at e2
  have e3 := (Submodule.Quotient.eq lineF).1 e2
  have := mem_lineF_apply_one e3
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_eq_same] at this
  exact (sub_eq_zero.1 this).symm

theorem fb_one_one_ne : fb d 1 1 ≠ 0 := fun h => by
  have := u_mul_fb d
  rw [h, mul_zero] at this
  exact zero_ne_one this

end Frame

section FrameLemmas

variable {c : Unit → Fin 2} {f : Ω} {b : Fin 2 → Fin 2 → Ω}

theorem frame_regular (hfr : IsFrameOver yLine (trivialBundle (segreCoord yLine) 2) c f b) (q p : Fin 2) :
    ∃ n : ℕ, f ^ n * b q p ∈ chartRing ℤ (segreCoord yLine) c := by
  obtain ⟨n, hn⟩ := (hfr.2.2.2.2 (b q)).2 ⟨fun q' => if q' = q then 1 else 0, fun q' => ⟨0, by
    show f ^ 0 * (if q' = q then (1 : Ω) else 0) ∈ _
    split_ifs <;> simp⟩, by simp only [ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ,
      if_true]⟩
  exact ⟨n, by simpa [smul_eq_mul] using mem_trivLat.1 hn p⟩

theorem frame_first_basis_vector (hfr : IsFrameOver yLine (trivialBundle (segreCoord yLine) 2) c f b) :
    ∃ a : Fin 2 → Ω, (∀ q, ∃ n : ℕ, f ^ n * a q ∈ chartRing ℤ (segreCoord yLine) c) ∧
      (Pi.single 0 1 : Fin 2 → Ω) = ∑ q, a q • b q := by
  refine (hfr.2.2.2.2 _).1 ⟨0, ?_⟩
  rw [pow_zero, one_smul]
  refine mem_trivLat.2 fun r => ?_
  by_cases h : r = 0
  · subst h; simp
  · simp [Pi.single_apply, h]

variable {z : (Σ _ : Unit, Fin 2) → ℂ}

theorem frame_value (hfr : IsFrameOver yLine (trivialBundle (segreCoord yLine) 2) c f b)
    (hz : z ⟨(), c ()⟩ ≠ 0) (hf : IsUnitAt yLine f z) (q p : Fin 2) :
    ∃ v, IsValueAt yLine (b q p) z v := by
  obtain ⟨n, hn⟩ := frame_regular hfr q p
  exact exists_isValueAt_of_pow_mul_mem (mem_mcPts_line.2 ⟨c (), hz⟩) (segreCoord_line_ne_zero (c ()))
    (fun _ => hz) hf hn

theorem gramAt_line (hz : ∃ i, z ⟨(), i⟩ ≠ 0) :
    gramAt lineMetric b z =
      (Matrix.of fun p q => valAt yLine (b q p) z)ᴴ * Matrix.of fun p q => valAt yLine (b q p) z := by
  classical
  obtain ⟨i, hi⟩ := hz
  have hl : ∃ l, InFrameDomain yLine (lineMetric.chart l) (lineMetric.fr l) z := ⟨i, inFrameDomain_line hi⟩
  have hS : ∃ S : Matrix (Fin 2) (Fin 2) Ω, ∀ q, b q = ∑ p, S p q • lineMetric.b hl.choose p :=
    ⟨Matrix.of fun p q => b q p, fun q => by
      funext r
      simp [lineMetric, Finset.sum_apply, Pi.single_apply]⟩
  have hSe : hS.choose = Matrix.of fun p q => b q p := by
    refine Matrix.ext fun p q => ?_
    have := congrFun (hS.choose_spec q) p
    simp [lineMetric, Finset.sum_apply, Pi.single_apply] at this
    exact this.symm
  unfold gramAt
  rw [dif_pos hl, dif_pos hS, hSe]
  show _ * (1 : Matrix (Fin 2) (Fin 2) ℂ) * _ = _
  rw [Matrix.mul_one]
  rfl

theorem quotNormSq_line (S : Matrix (Fin 2) (Fin 2) ℂ) (h10 : S 1 0 = 0) (h00 : S 0 0 ≠ 0) :
    quotNormSq (show 1 ≤ 2 by decide) (Sᴴ * S) = ‖S 1 1‖ ^ 2 := by
  unfold quotNormSq
  have hdet : (Sᴴ * S).det = ((‖S 0 0 * S 1 1‖ ^ 2 : ℝ) : ℂ) := by
    rw [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_fin_two, h10, mul_zero, sub_zero]
    rw [show star (S 0 0 * S 1 1) = (starRingEnd ℂ) (S 0 0 * S 1 1) from rfl, Complex.conj_mul']
    push_cast
    ring
  have hsub : ((Sᴴ * S).submatrix (headIdx (show 1 ≤ 2 by decide)) (headIdx (show 1 ≤ 2 by decide))).det =
      ((‖S 0 0‖ ^ 2 : ℝ) : ℂ) := by
    rw [Matrix.det_unique]
    have h0 : headIdx (show 1 ≤ 2 by decide) (default : Fin 1) = 0 := rfl
    simp only [Matrix.submatrix_apply, h0, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, h10,
      star_zero, zero_mul, add_zero]
    rw [show star (S 0 0) = (starRingEnd ℂ) (S 0 0) from rfl, Complex.conj_mul']
    push_cast
    ring
  rw [hdet, hsub, Complex.ofReal_re, Complex.ofReal_re, norm_mul, mul_pow]
  have : ‖S 0 0‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.2 h00)
  field_simp

end FrameLemmas

section Norm

variable {z : (Σ _ : Unit, Fin 2) → ℂ} (d : MuFrameAt (lineHodge II hII) z)

theorem frame_d : IsFrameOver yLine (trivialBundle (segreCoord yLine) 2) d.c d.f (fb d) :=
  (d.adapted ()).1

theorem norm_muFrameAt : d.norm = 1 := by
  have hzc : z ⟨(), d.c ()⟩ ≠ 0 := d.inDom.1 ()
  have hzP : z ∈ mcPts (mCoordIdeal yLine) := mem_mcPts_line.2 ⟨d.c (), hzc⟩
  have hf := d.inDom.2
  have hfr := frame_d d
  obtain ⟨v00, h00⟩ := frame_value hfr hzc hf 0 0
  obtain ⟨v11, h11⟩ := frame_value hfr hzc hf 1 1
  obtain ⟨nu, hnu⟩ := d.unit.2.1
  obtain ⟨vu, hu⟩ := exists_isValueAt_of_pow_mul_mem hzP (segreCoord_line_ne_zero (d.c ())) (fun _ => hzc) hf hnu
  have hu11 : vu * v11 = 1 := by
    have := isValueAt_mul hu h11
    rw [u_mul_fb d] at this
    exact isValueAt_one hzP this

  have hv00 : v00 ≠ 0 := by
    obtain ⟨a, ha, he⟩ := frame_first_basis_vector hfr
    have e1 := congrFun he 1
    have e0 := congrFun he 0
    simp only [Pi.single_apply, Fin.sum_univ_two, Finset.sum_apply, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, fb_zero_one d] at e1 e0
    change (0 : Ω) = a 0 * 0 + a 1 * fb d 1 1 at e1
    have ha1 : a 1 = 0 := by
      rw [mul_zero, zero_add] at e1
      exact (mul_eq_zero.1 e1.symm).resolve_right (fb_one_one_ne d)
    change (1 : Ω) = a 0 * fb d 0 0 + a 1 * fb d 1 0 at e0
    rw [ha1, zero_mul, add_zero] at e0
    obtain ⟨na, hna⟩ := ha 0
    obtain ⟨va, hva⟩ := exists_isValueAt_of_pow_mul_mem hzP (segreCoord_line_ne_zero (d.c ()))
      (fun _ => hzc) hf hna
    have := isValueAt_mul hva h00
    rw [← e0] at this
    have h1 := isValueAt_one hzP this
    intro h
    rw [h, mul_zero] at h1
    exact zero_ne_one h1
  have hS10 : valAt yLine (fb d 0 1) z = 0 := by rw [fb_zero_one d]; exact valAt_line_zero
  have hS00 : valAt yLine (fb d 0 0) z = v00 := valAt_eq hzP h00
  have hS11 : valAt yLine (fb d 1 1) z = v11 := valAt_eq hzP h11
  have hU : valAt yLine d.u z = vu := valAt_eq hzP hu
  show ‖valAt yLine d.u z‖ * (∏ k : Unit, ‖z ⟨k, d.c k⟩‖ ^ (0 : Unit → ℤ) k) *
    ∏ _τ : Unit, Real.sqrt (quotNormSq (show 1 ≤ 2 by decide) (gramAt lineMetric (fb d) z)) = 1
  rw [gramAt_line ⟨d.c (), hzc⟩, quotNormSq_line _ (by simpa using hS10) (by simpa [hS00] using hv00)]
  simp only [Pi.zero_apply, zpow_zero, Finset.prod_const_one, mul_one, Finset.univ_unique,
    Finset.prod_singleton, Matrix.of_apply]
  rw [Real.sqrt_sq (norm_nonneg _), hU, hS11, ← norm_mul, hu11, norm_one]

def stdFrameAt {z : (Σ _ : Unit, Fin 2) → ℂ} {i : Fin 2} (hi : z ⟨(), i⟩ ≠ 0) :
    MuFrameAt (lineHodge II hII) z where
  c _ := i
  f := 1
  inDom := inFrameDomain_line hi
  b _ := ⇑(Pi.basisFun Ω (Fin 2))
  adapted _ := ⟨isFrameOver_line i, (Pi.basisFun Ω (Fin 2)).span_eq, by
    show Submodule.span Ω (Set.range (⇑(Pi.basisFun Ω (Fin 2)) ∘ headIdx (show 1 ≤ 2 by decide))) = lineF
    have : Set.range (⇑(Pi.basisFun Ω (Fin 2)) ∘ headIdx (show 1 ≤ 2 by decide)) = {Pi.single 0 1} := by
      ext v
      simp only [Set.mem_range, Function.comp_apply, Set.mem_singleton_iff]
      constructor
      · rintro ⟨a, rfl⟩
        rw [Fin.fin_one_eq_zero a]
        simp [headIdx]
      · rintro rfl
        exact ⟨0, by simp [headIdx]⟩
    rw [this]
    rfl⟩
  u := 1
  unit := isUnitOn_one _ _ _
  eq := by
    show PiTensorProduct.tprod Ω (fun _ => quotWedge lineF (lineData II hII).j_le_N
      ⇑(Pi.basisFun Ω (Fin 2))) = _
    simp only [chartMono, lineHodge_aMu, Pi.zero_apply, zpow_zero, Finset.prod_const_one, one_mul, one_smul]
    rfl

theorem muMetric_line {z : (Σ _ : Unit, Fin 2) → ℂ} (hz : ∃ i, z ⟨(), i⟩ ≠ 0) :
    muMetric (lineHodge II hII) z = 1 := by
  classical
  obtain ⟨i, hi⟩ := hz
  have h : Nonempty (MuFrameAt (lineHodge II hII) z) := ⟨stdFrameAt hi⟩
  rw [muMetric, dif_pos h]
  exact norm_muFrameAt _

theorem muLine_h {z : (Σ _ : Unit, Fin 2) → ℂ} (hz : ∃ i, z ⟨(), i⟩ ≠ 0) :
    (muLine (lineHodge II hII)).h z = 1 := by
  have hom : IsHomogOfDeg (lineHodge II hII).aMu (muMetric (lineHodge II hII)) := by
    intro c w hc
    simp only [lineHodge_aMu, Pi.zero_apply, zpow_zero, Finset.prod_const_one, one_mul]
    by_cases hw : ∃ i, w ⟨(), i⟩ ≠ 0
    · obtain ⟨i, hi⟩ := hw
      rw [muMetric_line ⟨i, hi⟩, muMetric_line ⟨i, by simp [torusSmul, hc (), hi]⟩]
    · push_neg at hw
      have : torusSmul c w = w := by
        funext p
        obtain ⟨⟨⟩, i⟩ := p
        simp [torusSmul, hw i]
      rw [this]
  obtain ⟨i, hi⟩ := hz
  rw [muLine, hermOfFun_h hom (fun _ => ⟨i, hi⟩) (by rw [muMetric_line ⟨i, hi⟩]; exact one_pos),
    muMetric_line ⟨i, hi⟩]

theorem phMu_line {z : (Σ _ : Unit, Fin 2) → ℂ} (hz : ∃ i, z ⟨(), i⟩ ≠ 0) :
    phMu (lineHodge II hII) z = 0 := by
  rw [phMu, muLine_h hz, Real.log_one]

end Norm

theorem maDensity_eq_zero_of_eventually {φ : Fin 1 → (Fin 1 → ℂ) → ℝ} {y : Fin 1 → ℂ}
    (h : ∀ j, φ j =ᶠ[nhds y] fun _ => 0) : maDensity φ y = 0 := by
  have hH : ∀ j, cxHessian (φ j) y = 0 := by
    intro j
    have h2 : fderiv ℝ (fderiv ℝ (φ j)) y = fderiv ℝ (fderiv ℝ (fun _ : Fin 1 → ℂ => (0 : ℝ))) y :=
      (h j).fderiv.fderiv_eq
    ext a b
    simp [cxHessian, h2]
  simp [maDensity, mixedDisc, hH]

theorem degMu_line : degMu (lineHodge II hII) = 0 := by
  unfold degMu geomDeg ptsIntegral
  rw [lineData_n]
  split_ifs with hΨ
  · unfold ptsIntegralAt
    have : ∀ y : Fin 1 → ℂ, ∀ w, sheetDensity (mCoordIdeal (lineData II hII).y) hΨ.choose
        (fun _ z => Real.log ((muLine (lineHodge II hII)).h z)) (fun _ => 1) y w = 0 := by
      intro y w
      unfold sheetDensity
      split_ifs with hγ
      · rw [maDensity_eq_zero_of_eventually, mul_zero]
        intro j
        filter_upwards [hγ.choose_spec.2] with y' hy'
        rw [muLine_h (mem_mcPts_line.1 hy'.2.1), Real.log_one]
      · rfl
    simp [this]
  · rfl

theorem meanU_line : meanU (lineHodge II hII) (gaussCusp II hII) = 0 := by
  rw [meanU, degMu_line, div_zero]

end GroundTheory.Heights₂.Heights.LowerBoundFree.Line
