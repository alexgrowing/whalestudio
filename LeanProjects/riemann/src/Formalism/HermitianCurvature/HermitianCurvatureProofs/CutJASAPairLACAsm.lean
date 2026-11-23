import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASAPairLACCut

open MeasureTheory Topology Filter
open Formalism.FourierDecayAlt
open Formalism.REAL Formalism.QuantumDeterminants
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem gv_isClosed (k r : ℕ) : IsClosed (B.GV k r) := by
  show IsClosed {g : B.Mat k r | Matrix.conjTranspose g * Hpk k r * g = Hpk k r}
  exact isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
    continuous_const

theorem sgs_continuousAt_oneP {k r : ℕ} (g : B.Mat k r) :
    ContinuousAt (fun p : B.SS k r => B.sgs p g) oneP := by
  have hinv : ContinuousAt (fun A : B.Mat k r => A⁻¹) 1 := by
    refine continuousAt_matrix_inv _ ?_
    rw [Matrix.det_one]
    exact NormedRing.inverse_continuousAt (1 : ℂˣ)
  have c11 : Continuous fun p : B.SS k r => (Matrix.of p.1.1 : B.Mat k r) := continuous_fst.comp continuous_fst
  have c12 : Continuous fun p : B.SS k r => (Matrix.of p.1.2 : B.Mat k r) := continuous_snd.comp continuous_fst
  have c21 : Continuous fun p : B.SS k r => (Matrix.of p.2.1 : B.Mat k r) := continuous_fst.comp continuous_snd
  have c22 : Continuous fun p : B.SS k r => (Matrix.of p.2.2 : B.Mat k r) := continuous_snd.comp continuous_snd
  have i1 : ContinuousAt (fun p : B.SS k r => (Matrix.of p.1.1 : B.Mat k r)⁻¹) oneP :=
    ContinuousAt.comp_of_eq hinv c11.continuousAt rfl
  have i2 : ContinuousAt (fun p : B.SS k r => (Matrix.of p.1.2 : B.Mat k r)⁻¹) oneP :=
    ContinuousAt.comp_of_eq hinv c12.continuousAt rfl
  show ContinuousAt (fun p : B.SS k r => (Matrix.of p.1.1 : B.Mat k r)⁻¹ * (Matrix.of p.1.2 : B.Mat k r)⁻¹ * g *
    (Matrix.of p.2.2 : B.Mat k r) * (Matrix.of p.2.1 : B.Mat k r)) oneP
  exact (((i1.mul i2).mul continuousAt_const).mul c22.continuousAt).mul c21.continuousAt

theorem avgCutoff_of_parts (hB : ACBump) (hI : ACInv) (hN : ACInt) (hP : ACHaarPos) (hS : ACSmooth) :
    Formalism.FourierDecayAlt.P.JFxI.AvgCutoff := by
  intro k r Wp Wq _ _ _ _ D K hK hKQ
  obtain ⟨φ₀, hφ₀s, hφ₀n, hφ₀c, hφ₀O, hφ₀K⟩ := hB k r Wp Wq D K hK hKQ
  have hφ₀cont : Continuous φ₀ := hφ₀s.continuous
  set I : B.Mat k r → ℝ := fun g => ∫ p, φ₀ (B.sgs p g) ∂D.μSS with hIdef
  have hgqOm : ∀ q ∈ JF.QDom k r D.z D.z', B.gq D q ∈ JF.Om k r D.z D.z' := fun q hq =>
    Formalism.FourierDecayAlt.P.big_cell_domain k r Wp Wq D q hq

  have hposI : ∀ g ∈ JF.Om k r D.z D.z', 0 < φ₀ g → 0 < I g := by
    intro g hg hφg
    have hint := hN k r Wp Wq D φ₀ hφ₀cont hφ₀c g hg
    rw [hIdef]
    refine (integral_pos_iff_support_of_nonneg (fun p => hφ₀n _) hint).2 ?_
    have hca : ContinuousAt (fun p : B.SS k r => φ₀ (B.sgs p g)) oneP :=
      hφ₀cont.continuousAt.comp (sgs_continuousAt_oneP g)
    have hev : ∀ᶠ p in 𝓝 (oneP : B.SS k r), 0 < φ₀ (B.sgs p g) := by
      refine hca.eventually (lt_mem_nhds ?_)
      show 0 < φ₀ (B.sgs oneP g)
      rw [sgs_oneP]; exact hφg
    obtain ⟨O, hOsub, hOo, hO1⟩ := mem_nhds_iff.1 hev
    exact lt_of_lt_of_le (hP k r Wp Wq D O hOo hO1)
      (measure_mono fun p hp => (ne_of_gt (hOsub hp)))

  have hcont : ContinuousOn (fun q => I (B.gq D q)) K := by
    intro q₀ hq₀
    have hq₀D := hKQ hq₀
    obtain ⟨U, I', hUo, hgU, hI'U, hII'⟩ := hS k r Wp Wq D φ₀ hφ₀s hφ₀c hφ₀O _ (hgqOm q₀ hq₀D)
    have hgqc : ContinuousAt (fun q => B.gq D q) q₀ :=
      ((Formalism.FourierDecayAlt.P.BigCellOpenDomain.gq_contDiffOn D 0).continuousOn).continuousAt
        ((Formalism.FourierDecayAlt.P.BigCellOpenDomain.qdom_open D.z D.z').mem_nhds hq₀D)
    have hev : (fun q => I (B.gq D q)) =ᶠ[𝓝 q₀] fun q => I' (B.gq D q) := by
      have h1 : ∀ᶠ q in 𝓝 q₀, B.gq D q ∈ U := hgqc.preimage_mem_nhds (hUo.mem_nhds hgU)
      have h2 : ∀ᶠ q in 𝓝 q₀, q ∈ JF.QDom k r D.z D.z' := (Formalism.FourierDecayAlt.P.BigCellOpenDomain.qdom_open D.z D.z').mem_nhds hq₀D
      filter_upwards [h1, h2] with q hq1 hq2
      exact hII' _ hq1 (hgqOm q hq2).1
    have hI'c : ContinuousAt I' (B.gq D q₀) := (hI'U.continuousOn).continuousAt (hUo.mem_nhds hgU)
    exact ((ContinuousAt.comp_of_eq hI'c hgqc rfl).congr hev.symm).continuousWithinAt

  obtain ⟨c₀, hc₀, hc₀K⟩ : ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ q ∈ K, c₀ ≤ I (B.gq D q) := by
    rcases K.eq_empty_or_nonempty with hKe | hKne
    · exact ⟨1, one_pos, fun q hq => by simp [hKe] at hq⟩
    · obtain ⟨q₁, hq₁, hmin⟩ := hK.exists_isMinOn hKne hcont
      exact ⟨I (B.gq D q₁), hposI _ (hgqOm q₁ (hKQ hq₁)) (hφ₀K q₁ hq₁), fun q hq => hmin hq⟩

  set s : ℝ → ℝ := fun t => Real.smoothTransition ((t - c₀ / 2) / (c₀ / 2)) with hsdef
  set σ : ℝ → ℝ := fun t => s t * t + (1 - s t) * (c₀ / 2) with hσdef
  have hc2 : 0 < c₀ / 2 := by linarith
  have hσlb : ∀ t, c₀ / 2 ≤ σ t := by
    intro t
    have h0 : 0 ≤ s t := Real.smoothTransition.nonneg _
    by_cases ht : c₀ / 2 ≤ t
    · show c₀ / 2 ≤ s t * t + (1 - s t) * (c₀ / 2)
      nlinarith
    · have hz : s t = 0 := Real.smoothTransition.zero_of_nonpos
        (div_nonpos_of_nonpos_of_nonneg (by linarith) hc2.le)
      show c₀ / 2 ≤ s t * t + (1 - s t) * (c₀ / 2)
      rw [hz]; simp
  have hσpos : ∀ t, σ t ≠ 0 := fun t => (lt_of_lt_of_le hc2 (hσlb t)).ne'
  have hσid : ∀ t, c₀ ≤ t → σ t = t := by
    intro t ht
    have h1 : s t = 1 := Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ hc2]; linarith)
    show s t * t + (1 - s t) * (c₀ / 2) = t
    rw [h1]; ring
  have hσs : ContDiff ℝ ∞ σ := by
    have hs : ContDiff ℝ ∞ s :=
      Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)
    exact (hs.mul contDiff_id).add ((contDiff_const.sub hs).mul contDiff_const)

  classical
  let φ : B.Mat k r → ℂ := fun g => if g ∈ B.GV k r then ((φ₀ g * (σ (I g))⁻¹ : ℝ) : ℂ) else 0
  have hφ0 : ∀ g, g ∉ tsupport φ₀ → φ g = 0 := by
    intro g hg
    have : φ₀ g = 0 := image_eq_zero_of_notMem_tsupport hg
    simp [φ, this]
  refine ⟨φ, ?_, ⟨tsupport φ₀ ∩ B.GV k r, hφ₀c.isCompact.inter_right (gv_isClosed k r),
    fun g hg => ⟨hg.2, hφ₀O hg.1⟩, fun g hg => ?_⟩, ?_⟩
  ·
    intro g₀ hg₀
    by_cases hO : g₀ ∈ Q.OmPlus k r D.z D.z'
    · obtain ⟨U, I', hUo, hgU, hI'U, hII'⟩ := hS k r Wp Wq D φ₀ hφ₀s hφ₀c hφ₀O g₀ ⟨hg₀, hO⟩
      refine ⟨U, fun g => ((φ₀ g * (σ (I' g))⁻¹ : ℝ) : ℂ), hUo, hgU, ?_, ?_⟩
      · have h1 : ContDiffOn ℝ ∞ (fun g => φ₀ g * (σ (I' g))⁻¹) U :=
          hφ₀s.contDiffOn.mul ((hσs.comp_contDiffOn hI'U).inv fun g _ => hσpos _)
        exact Complex.ofRealCLM.contDiff.comp_contDiffOn h1
      · intro g hg hgG
        show (if g ∈ B.GV k r then ((φ₀ g * (σ (∫ p, φ₀ (B.sgs p g) ∂D.μSS))⁻¹ : ℝ) : ℂ) else 0) = _
        rw [if_pos hgG, hII' g hg hgG]
    · refine ⟨(tsupport φ₀)ᶜ, fun _ => 0, (isClosed_tsupport _).isOpen_compl, fun h => hO (hφ₀O h),
        contDiffOn_const, fun g hg _ => hφ0 g hg⟩
  ·
    by_cases hgG : g ∈ B.GV k r
    · exact hφ0 g fun h => hg ⟨h, hgG⟩
    · simp [φ, hgG]
  ·
    intro p₀ hp₀ q hq
    have hgq := hgqOm q (hKQ hq)
    have hg := Formalism.FourierDecayAlt.P.PositiveOrbitOpen.sgs_Om D hp₀ hgq
    have hIg : I (B.sgs p₀ (B.gq D q)) = I (B.gq D q) := hI k r Wp Wq D φ₀ hφ₀cont p₀ hp₀ _
    have hIpos : 0 < I (B.gq D q) := lt_of_lt_of_le hc₀ (hc₀K q hq)
    have hae : ∀ᵐ p ∂D.μSS, φ (B.sgs p (B.sgs p₀ (B.gq D q))) =
        ((φ₀ (B.sgs p (B.sgs p₀ (B.gq D q))) * (I (B.gq D q))⁻¹ : ℝ) : ℂ) := by
      filter_upwards [Formalism.FourierDecayAlt.P.B5.ae_inSS D] with p hp
      have hG : B.sgs p (B.sgs p₀ (B.gq D q)) ∈ B.GV k r := Formalism.FourierDecayAlt.P.PositiveOrbitOpen.sgs_GV D hp hg.1
      have hIp : I (B.sgs p (B.sgs p₀ (B.gq D q))) = I (B.gq D q) := by
        rw [← hIg]; exact hI k r Wp Wq D φ₀ hφ₀cont p hp _
      simp only [φ, if_pos hG, hIp, hσid _ (hc₀K q hq)]
    rw [integral_congr_ae hae, integral_complex_ofReal, integral_mul_const]
    change (((I (B.sgs p₀ (B.gq D q))) * (I (B.gq D q))⁻¹ : ℝ) : ℂ) = 1
    rw [hIg, mul_inv_cancel₀ hIpos.ne', Complex.ofReal_one]

end Formalism.FourierDecayAlt.P.CutMP.JA.SA
